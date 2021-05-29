import inst.network.basic
open reactor
open reactor.ports

open_locale classical

-- The type of opaque values that underlie TPAs.
-- Their equality has to be decidable, but beyond that their values are of no interest.
variables (υ : Type*) [decidable_eq υ]

-- A tag is a logical timestamp: the first component is the time value, the second component is
-- the microstep index. Their ordering is lexicographical.
@[derive has_le, derive has_lt]
def tag := lex ℕ ℕ  

-- A TPA is a finite set of tag-value pairs where each tag is unique. 
-- They are the primitive values used in timed reactor networks.
-- Since instantaneous networks wrap their primitive values in `option`, 
-- we require TPAs to be non-empty in order to avoid two versions of the absent value.
structure tpa := 
  (pairs : finset (tag × υ))
  (unique: ∀ p p' ∈ pairs, prod.fst p = prod.fst p' → p = p')
  (nonempty : pairs.nonempty)

variable {υ}

def tpa.map (tp : tpa υ) : tag → set υ := 
  λ t, { v | (t, v) ∈ tp.pairs }

lemma tpa.map_subsingleton (tp : tpa υ) (t : tag) : (tp.map t).subsingleton :=
  begin
    unfold set.subsingleton tpa.map,
    intros x hₓ x' hₓ',
    rw set.mem_set_of_eq at hₓ hₓ',
    have h, from tp.unique _ _ hₓ hₓ',
    replace h := h (refl _),
    injection h
  end

noncomputable def tpa.map' (tp : tpa υ) : tag → option υ := λ t, 
  (tp.map_subsingleton t)
    .eq_empty_or_singleton
    .by_cases (λ _, none) (λ s, s.some)

-- An action edge connects an output action port (OAP) to an input action port (IAP).
@[ext]
structure timed.network.action_edge := 
  (oap : port.id)
  (iap : port.id)

open timed.network

-- Action edges' equality is non-constructively decidable.
noncomputable instance timed.network.action_edge_dec_eq : decidable_eq action_edge := classical.dec_eq _

-- The proposition that there can be at most one action edge per OAP.
def finset.are_many_to_one (es : finset action_edge) : Prop :=
  ∀ e e' : action_edge, e ∈ es → e' ∈ es → e.oap = e'.oap → e = e'

-- The proposition that action edges don't connect between different reactors.
def finset.are_local (es : finset action_edge) : Prop :=
  ∀ e : action_edge, e ∈ es → e.oap.rtr = e.iap.rtr

-- The proposition that an OAP has exactly one incoming connection.
def finset.have_one_src_in (es : finset action_edge) (σ : inst.network (tpa υ)) : Prop :=
  ∀ e : action_edge, e ∈ es → 
  ∃! r : reaction.id, 
    (e.oap ∈ σ.η.deps r role.output)

-- The proposition that a reaction can not connect to the same IAP through multiple OAPs.
def finset.are_functionally_unique_in (es : finset action_edge) (σ : inst.network (tpa υ)) : Prop :=
  ∀ (e e' : action_edge) (r : reaction.id), e ∈ es → e' ∈ es → 
    (e.oap ∈ σ.η.deps r role.output) → (e'.oap ∈ σ.η.deps r role.output) → 
    e.iap = e'.iap → e.oap = e'.oap

-- The proposition that action ports do not also behave as regular ports (by being connected
-- with network graph edges).
def finset.are_separate_from (es : finset action_edge) (σ : inst.network (tpa υ)) : Prop :=
  ∀ (ae : action_edge) (ne : inst.network.graph.edge), ae ∈ es → ne ∈ σ.η.edges → 
    ae.iap ≠ ne.dst ∧ ae.oap ≠ ne.src

-- A given set of action edges (and by extension action ports) is well-formed for a given
-- instantaneous network, if all of the properties above hold.
def finset.are_well_formed_for (es : finset action_edge) (σ : inst.network (tpa υ)) : Prop :=
  es.are_many_to_one ∧ 
  es.are_local ∧
  es.have_one_src_in σ ∧ 
  es.are_functionally_unique_in σ ∧
  es.are_separate_from σ

-- Wellformedness of action edges is retained under equivalence of instantaneous reactor networks.
lemma timed.network.equiv_inst_network_wf (es : finset action_edge) {σ σ' : inst.network (tpa υ)} (hq : σ' ≈ σ) (hw : es.are_well_formed_for σ) : 
  es.are_well_formed_for σ' :=
  begin
    unfold finset.are_well_formed_for at hw ⊢,
    simp only [(≈)] at hq,
    repeat { split },
      simp [hw],
      simp [hw],
      {
        unfold finset.have_one_src_in inst.network.graph.deps inst.network.graph.rcn at ⊢ hw,
        intros e hₑ,
        obtain ⟨i, hᵢ⟩ := hw.right.right.left e hₑ,
        rw exists_unique,
        existsi i,
        split,
          { 
            rw (hq.right.right i.rtr).right,
            exact hᵢ.left
          },
          { 
            intro x,
            rw (hq.right.right x.rtr).right,
            exact hᵢ.right x
          }
      },
      {
        unfold finset.are_functionally_unique_in inst.network.graph.deps inst.network.graph.rcn,
        intros e e' i,
        rw (hq.right.right i.rtr).right,
        exact hw.right.right.right.left e e' i
      },
      {
        unfold finset.are_separate_from,
        rw hq.left,
        exact hw.right.right.right.right
      }
  end

variable (υ)

-- A timed reactor network wraps an instantaneous reactor network and equips it with actions 
-- (via action-ports and -edges), as well as timed execution.
structure timed.network :=
  (σ : inst.network (tpa υ))
  (time : tag)
  (events : port.id → tag → option υ)
  (actions : finset action_edge)
  (well_formed : actions.are_well_formed_for σ)

namespace timed
namespace network

  variable {υ}

  -- The input action ports for a given timed network.
  noncomputable def iaps (τ : timed.network υ) : finset port.id := τ.actions.image (λ e, e.iap)

  -- The output action ports for a given timed network.
  noncomputable def oaps (τ : timed.network υ) : finset port.id := τ.actions.image (λ e, e.oap)

  def iap_has_oap (τ : timed.network υ) (iap : port.id) (oap : port.id) : Prop :=
    ∃ ae ∈ τ.actions, ae = { oap := oap, iap := iap }

  lemma iap_has_finite_oaps (τ : timed.network υ) (iap : port.id) : { oap | τ.iap_has_oap iap oap }.finite :=
    sorry

  -- The set of OAPs connected to a given IAP.
  noncomputable def oaps_for_iap (τ : timed.network υ) (iap : port.id) : finset port.id :=
    (iap_has_finite_oaps τ iap).to_finset

  lemma oaps_for_iap_mem {τ : timed.network υ} {iap oap : port.id} (h : oap ∈ τ.oaps_for_iap iap) : oap ∈ τ.oaps :=  
    sorry

  -- The set of OAPs connected to a given IAP.
  noncomputable def oaps_for_iap' (τ : timed.network υ) (iap : port.id) : finset { oap // oap ∈ τ.oaps } :=
    (τ.oaps_for_iap iap).attach.image (λ oap, subtype.mk ↑oap (oaps_for_iap_mem oap.property))

  -- A lifted version of `reactor.rcns_dep_to`.
  def rcns_dep_to (τ : timed.network υ) (r : ports.role) (p : port.id) : set reaction.id :=
    ((τ.σ.η.rtr p.rtr).rcns_dep_to r p.prt).image (reaction.id.mk p.rtr)

  -- This is a different way of expressing of `finset.have_one_src_in`, which is more suitable for use in `src_for_oap`.
  lemma rcns_dep_to_oap_singleton (τ : timed.network υ) (oap : port.id) (h : oap ∈ τ.oaps) : 
    ∃ r, (τ.rcns_dep_to role.output oap) = {r} :=
    sorry

  -- The unique reaction connected to a given OAP.
  noncomputable def src_for_oap (τ : timed.network υ) (oap : port.id) (h : oap ∈ τ.oaps) : reaction.id :=
    (rcns_dep_to_oap_singleton τ oap h).some

  -- The priority of a given OAP is the priority of the reaction it is connected to.
  noncomputable def priority_for_oap (τ : timed.network υ) (oap : port.id) (h : oap ∈ τ.oaps) : ℕ :=
    (τ.src_for_oap oap h).priority

  def oap_lt {τ : timed.network υ} (oap oap' : { o // o ∈ τ.oaps }) : Prop :=
    τ.priority_for_oap ↑oap oap.property < τ.priority_for_oap ↑oap' oap'.property

  instance {τ : timed.network υ} : is_trans _ (@oap_lt _ _ τ) := sorry
  instance {τ : timed.network υ} : is_antisymm _ (@oap_lt _ _ τ) := sorry
  instance {τ : timed.network υ} : is_total _ (@oap_lt _ _ τ) := sorry

  -- The tags for which the given timed network has events scheduled.
  -- Note that this set also contains all tags from past events.
  def event_tags (τ : timed.network υ) : set tag :=
    { t | ∃ (m : tag → option υ) (h : m ∈ τ.oaps.image τ.events), m t ≠ none }

  -- The proposition that a given tag is the next tag for which a given network has a scheduled event.
  def tag_is_next (τ : timed.network υ) (t : tag) : Prop :=
    t ∈ τ.event_tags ∧ (t > τ.time) ∧ (∀ t' ∈ τ.event_tags, t' > τ.time → t' ≥ t)

  -- There can only ever be at most one next tag.
  lemma next_tags_subsingleton (τ : timed.network υ) :
    { t | τ.tag_is_next t }.subsingleton :=
    sorry

  -- The least tag that after the current `time`, for which there exists a port that has a non-`none` value at that tag.
  -- I.e. the next tag at which an event occurs.
  noncomputable def next_tag (τ : timed.network υ) : option tag :=
    (next_tags_subsingleton τ)
      .eq_empty_or_singleton
      .by_cases (λ _, none) (λ s, s.some)

end network
end timed
