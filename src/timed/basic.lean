import inst.network.basic
open reactor.ports

-- The type of opaque values that underlie TPAs.
-- Their equality has to be decidable, but beyond that their values are of no interest.
variables (υ : Type*) [decidable_eq υ]

-- A tag is a logical timestamp: the first component is the time value, the second component is
-- the microstep index. Their ordering is lexicographical.
@[derive has_le]
def tag := lex ℕ ℕ  

-- A tpa is a set of tag-value pairs. They are the primitive values used in timed reactor networks.
@[derive has_union, derive has_emptyc, derive has_sep (tag × option υ), derive has_mem (tag × option υ)]
def tpa := finset (tag × option υ)

variable {υ}

-- Merges a given TPA *onto* another TPA.
-- Any tags that are assigned in both TPAs are made unique by choosing the assignment from the first TPA.
def tpa.merge : option (tpa υ) → option (tpa υ) → option (tpa υ)
  | none     none      := none
  | (some t) none      := some t
  | none     (some t') := some t'
  | (some t) (some t') := some (t ∪ (t'.filter (λ tv, tv.1 ∉ t.image (prod.fst))))

-- Returns a TPA that only contains at most the tag-value pair for a given tag (if there is one).
def tpa.at_tag : option (tpa υ) → tag → option (tpa υ)
  | none     _ := none
  | (some t) g := let t' := t.filter (λ tv, tv.1 = g) in if t' = ∅ then none else some t'

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

-- The proposition that an OAP has at most one incoming connection.
def finset.have_unique_source_in (es : finset action_edge) (σ : inst.network (tpa υ)) : Prop :=
  ∀ (e : action_edge) (r r' : reaction.id), e ∈ es → 
    (e.oap ∈ σ.η.deps r role.output) → (e.oap ∈ σ.η.deps r' role.output) → r = r

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
  es.have_unique_source_in σ ∧ 
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
        unfold finset.have_unique_source_in inst.network.graph.deps inst.network.graph.rcn,
        intros e i i',
        rw [(hq.right.right i.rtr).right, (hq.right.right i'.rtr).right],
        exact hw.right.right.left e i i'
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
  (event_queue : list tag)
  (actions : finset action_edge)
  (well_formed : actions.are_well_formed_for σ)

namespace timed
namespace network

  variable {υ}

  -- The input action ports for a given timed network.
  noncomputable def iaps (τ : timed.network υ) : finset port.id := τ.actions.image (λ e, e.iap)

  -- The output action ports for a given timed network.
  noncomputable def oaps (τ : timed.network υ) : finset port.id := τ.actions.image (λ e, e.oap)

  -- The priority of a given action edge is the priority of the reaction its OAP is connected to.
  -- By the property `are_functionally_unique_in`, there is at most one of those reactions.
  -- If there is none, `none` is returned. 
  noncomputable def action_edge.priority_in (ae : action_edge) (σ : inst.network (tpa υ)) : option ℕ :=
    let rtr := (σ.η.rtr ae.oap.rtr) in
    let rcns := rtr.priorities.filter (λ p, p ∈ (rtr.reactions ae.oap.prt).dₒ) in
    if h : rcns.card = 1 then (finset.card_eq_one.mp h).some else none

  -- The order of action edges is determined by their priorities (`action_edge.priority_in`).
  -- If there is no priority for an edge, it is considered smaller than all other edges.
  -- Comparing these values across different reactors doesn't really make sense.
  def action_priority_ge (σ : inst.network (tpa υ)) : action_edge → action_edge → Prop := 
    λ e e',
      match e.priority_in σ, e'.priority_in σ with
      | some p, some p' := p ≥ p'
      | _,      none    := true
      | none,   _       := false
      end

  -- The `action_priority_ge` relation is non-constructively decidable.
  noncomputable instance {σ : inst.network (tpa υ)} : decidable_rel (action_priority_ge σ) := classical.dec_rel _

end network
end timed
