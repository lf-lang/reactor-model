import timed.primitives
import timed.actions
import timed.events
open reactor
open reactor.ports

open_locale classical

-- The type of opaque values that underlie TPAs.
-- Their equality has to be decidable, but beyond that their values are of no interest.
variables (υ : Type*) [decidable_eq υ]

open timed.network

-- A timed reactor network wraps an instantaneous reactor network and equips it with 
-- a current time (-tag), actions, events and timed execution.
@[ext]
structure timed.network :=
  (σ : inst.network (tpa υ))
  (time : tag)
  (μ : event_map υ)
  (actions : finset action_edge)
  (well_formed : actions.are_well_formed_for σ)

namespace timed
namespace network

  variable {υ} 

  -- The input action ports for a given timed network.
  -- These can simply be extracted from the network's action edges.
  noncomputable def iaps (τ : timed.network υ) : finset port.id := 
    τ.actions.image (λ e, e.iap)

  -- The output action ports for a given timed network.
  -- These can simply be extracted from the network's action edges.
  noncomputable def oaps (τ : timed.network υ) : finset port.id := 
    τ.actions.image (λ e, e.oap)

  -- An equivalence proposition for what it means to be an OAP for a given network.
  lemma oaps_mem {τ : timed.network υ} {oap : port.id} : 
    oap ∈ τ.oaps ↔ (∃ iap, (action_edge.mk oap iap) ∈ τ.actions) :=
    begin
      unfold oaps,
      rw finset.mem_image,
      split,
        {
          intro h,
          obtain ⟨e, hₑ, hₒ⟩ := h,
          existsi e.iap,
          rw ←hₒ,
          have h' : e = action_edge.mk e.oap e.iap, by { ext1, simp },
          rw ←h',
          exact hₑ
        },
        {
          intro h,
          obtain ⟨iap, hₘ⟩ := h,
          exact ⟨action_edge.mk oap iap, hₘ, by simp⟩
        }
    end

  -- The proposition that a given IAP is connected to a given OAP.
  -- This property is trivially stated, but is defined separately anyway as it
  -- is used for further definitions below (notably as the starting point for `oaps_for_iap`).
  def iap_has_oap (τ : timed.network υ) (iap : port.id) (oap : port.id) : Prop :=
    { action_edge . oap := oap, iap := iap } ∈ τ.actions

  -- Any given IAP is connected to only finitely many OAPs.
  -- Since a reactor network can only contain finitely many actions edges (it's a `finset`), 
  -- this property trivially holds (on intuitive level).
  lemma iap_has_finite_oaps (τ : timed.network υ) (iap : port.id) : { oap | τ.iap_has_oap iap oap }.finite :=
    begin
      unfold set.finite,
      suffices f : fintype ↥{oap : port.id | τ.iap_has_oap iap oap}, from ⟨f⟩,
      sorry
    end 

  -- The (finite) set of OAPs connected to a given IAP.
  noncomputable def oaps_for_iap (τ : timed.network υ) (iap : port.id) : finset port.id :=
    (iap_has_finite_oaps τ iap).to_finset

  -- If a given port is in the set of OAPs for some IAP (returned as part of `oaps_for_iap`),
  -- then it is also in the set of OAPs of the corresponding network (`oaps`).
  -- This property is simply a technicality used to define `oaps_for_iap'`.
  lemma oaps_for_iap_mem {τ : timed.network υ} {iap oap : port.id} (h : oap ∈ τ.oaps_for_iap iap) : oap ∈ τ.oaps :=  
    begin
      rw oaps_mem,
      simp only [oaps_for_iap, set.finite.mem_to_finset, iap_has_oap] at h,
      existsi iap,
      simp only [set.mem_def, set.set_of_app_iff] at h,
      exact h
    end

  -- The set of OAPs connected to a given IAP with a proof of `oap ∈ τ.oaps` attached for each `oap`.
  -- This build directly on the definition of `oaps_for_iap`.
  noncomputable def oaps_for_iap' (τ : timed.network υ) (iap : port.id) : finset { oap // oap ∈ τ.oaps } :=
    (τ.oaps_for_iap iap).attach.image (λ oap, subtype.mk ↑oap (oaps_for_iap_mem oap.property))

  -- A lifted version of `reactor.rcns_dep_to`.
  -- This is the starting point for the definition of `src_for_oap`.
  def rcns_dep_to (τ : timed.network υ) (r : ports.role) (p : port.id) : set reaction.id :=
    ((τ.σ.η.rtr p.rtr).rcns_dep_to r p.prt).image (reaction.id.mk p.rtr)

  -- This is a different way of expressing `finset.have_one_src_in`, 
  -- which is more suitable for use in `src_for_oap`.
  lemma rcns_dep_to_oap_singleton {τ : timed.network υ} {oap : port.id} (h : oap ∈ τ.oaps) : 
    ∃ r, (τ.rcns_dep_to role.output oap) = {r} :=
    sorry

  -- The unique reaction connected to a given OAP.
  -- This property is only defined when the given port is proven to be an OAP.
  -- For all other ports, we wouldn't be able to define this property.
  noncomputable def src_for_oap (τ : timed.network υ) {oap : port.id} (h : oap ∈ τ.oaps) : reaction.id :=
    (rcns_dep_to_oap_singleton h).some

  -- The source of an OAP (the reaction it is connected to) lives in the same reactor
  -- as the OAP itself.
  -- This lemma is ultimately used to show that `oap_le` is antisymmetric.
  lemma oap_src_eq_rtr {τ : timed.network υ} {oap : port.id} (h : oap ∈ τ.oaps) : 
    (τ.src_for_oap h).rtr = oap.rtr :=
    begin
      unfold src_for_oap,
      have h', from set.mem_singleton (rcns_dep_to_oap_singleton h).some,
      rw ←(Exists.some_spec (rcns_dep_to_oap_singleton h)) at h',
      simp only [rcns_dep_to, set.mem_image] at h',
      obtain ⟨_, _, he⟩ := h',
      unfold Exists.some at ⊢ he,
      -- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Injection.20failing
      sorry 
    end
  
  -- If two OAPs have the same source (are connected to the same reaction), 
  -- then they must be the same OAP. This is a result of `have_one_src_in` property
  -- of action edges in timed networks.
  -- This lemma is ultimately used to show that `oap_le` is antisymmetric.
  lemma eq_src_eq_oap {τ : timed.network υ} {oap oap' : port.id} {hₘ : oap ∈ τ.oaps} {hₘ' : oap' ∈ τ.oaps} (h : τ.src_for_oap hₘ = τ.src_for_oap hₘ') : 
    oap = oap' :=
    -- This should be similar to the proof of `oap_src_eq_rtr` above.
    sorry 

  -- The priority for a given OAP is the priority of the (unique) reaction it is connected to.
  --
  -- The OAP's reactor's ID is added as part of the priority (now ℕ × ℕ instead of just ℕ),
  -- to make sure that each OAP in a *network* has a unique priority.
  -- This makes ordering them (in `oap_le`) a bit easier, without any loss of generality.
  --
  -- This property is only defined when the given port is proven to be an OAP.
  -- For all other ports, we wouldn't be able to define this property (cf. the documentation 
  -- for `src_for_oap`).
  noncomputable def priority_for_oap (τ : timed.network υ) (oap : port.id) (h : oap ∈ τ.oaps) : lex ℕ ℕ :=
    (oap.rtr, (τ.src_for_oap h).priority)

  -- No two (different) OAPs have the same priority.
  lemma unique_oap_priority 
    {τ : timed.network υ} {oap oap' : port.id} {hₘ : oap ∈ τ.oaps} {hₘ' : oap' ∈ τ.oaps} 
    (h : τ.priority_for_oap oap hₘ = τ.priority_for_oap oap' hₘ') : 
    oap = oap' :=
    begin
      unfold priority_for_oap reaction.id.priority at h,
      injection h with hr hp,
      clear h,
      have hs, from oap_src_eq_rtr hₘ,
      have hs', from oap_src_eq_rtr hₘ',
      have h : τ.src_for_oap hₘ = τ.src_for_oap hₘ', {
        rw hr at hs,
        have hs_eq, from eq.trans hs (symm hs'),
        ext ; assumption
      },
      exact eq_src_eq_oap h,
    end

  -- A predicate for sorting OAPs by their priority.
  -- We require the OAPs to be given as instances of the subtype `{ o // o ∈ τ.oaps }`,
  -- because only then can we ensure that we can associate a priority with the port
  -- (cf. the documentation for `priority_for_oap`).
  def oap_le {τ : timed.network υ} (oap oap' : { o // o ∈ τ.oaps }) : Prop :=
    τ.priority_for_oap ↑oap oap.property ≤ τ.priority_for_oap ↑oap' oap'.property

  -- `oap_le` is transitive.
  instance {τ : timed.network υ} : is_trans _ (@oap_le _ _ τ) := ⟨begin
    intros a b c,
    unfold oap_le,
    exact trans
  end⟩

  -- `oap_le` is antisymmetric.
  instance {τ : timed.network υ} : is_antisymm _ (@oap_le _ _ τ) := ⟨begin
    intros a b,
    unfold oap_le,
    intros h h',
    exact subtype.ext (unique_oap_priority (le_antisymm h h'))
  end⟩ 

  -- `oap_le` is total.
  instance {τ : timed.network υ} : is_total _ (@oap_le _ _ τ) := ⟨begin
    intros a b,
    unfold oap_le,
    apply le_total
  end⟩

  -- The events contained in the OAPs of the given network, represented as an event-map.
  -- This property is really only sensible for post-instantaneous networks.  
  -- 
  -- Obtaining this map is non-trivial, because each IAP may have multiple OAPs which contain
  -- a tag-value pair for any given tag. Hence the (tag → value) map associated with a given IAP
  -- has to return the value of the OAP with the lowest priority (the OAP that was written to *last*),
  -- where the value for the tag is not `none`.
  noncomputable def new_events (τ : timed.network υ) : event_map υ := 
    λ iap t, ((τ.oaps_for_iap' iap).sort oap_le).mfirst (λ oap, (τ.σ.η.port role.output oap) >>= (λ o, o.map t))

  noncomputable def all_events (τ : timed.network υ) : event_map υ := 
    (λ p t, τ.new_events p t <|> τ.μ p t)

  -- The next tag (after its current time), for which the network has
  -- a scheduled event (if there is any).
  noncomputable def next_tag (τ : timed.network υ) : option tag :=
    τ.all_events.next_tag_after τ.time

end network
end timed
