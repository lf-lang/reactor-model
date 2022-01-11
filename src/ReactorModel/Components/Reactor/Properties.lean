import ReactorModel.Components.Reactor.Projections

open Port

variable {ι υ} [Value υ]

namespace Reactor

-- The `roles` map associates each port (ID) in a reactor with a role (input or output).
-- These mappings should exist only for *those* ports with are actually part of the reactor,
-- which is enforced by this constraint.
theorem wfRoles (rtr : Reactor ι υ) : rtr.roles.ids = rtr.ports.ids := rtr.rawWF.direct.wfRoles

-- TODO (maybe): Factor out the overlap between the proofs of `wfNormDeps` and `wfMutDeps`.

-- This constraint constrains the anti/-dependencies of `rtr`'s normal reactions, such that:
-- 1. their dependencies can only be input ports of `rtr` or output ports of reactors
--    nested directly in `rtr`
-- 2. their antidependencies can only be output ports of `rtr` or input ports of reactors
--    nested directly in `rtr`
theorem wfNormDeps {rtr : Reactor ι υ} {n : Reaction ι υ} (r : Port.Role) (h : n ∈ rtr.norms.values) : 
  n.deps r ⊆ rtr.acts.ids ∪ (rtr.ports' r).ids ∪ rtr.nestedPortIDs r.opposite := by
  simp only [Finset.subset_iff, Finset.mem_union]
  intro j hj
  simp only [norms, Finmap.filter'_mem_values] at h
  obtain ⟨i, h, hn⟩ := h
  obtain ⟨nr, hr⟩ := rcns_has_raw h
  have he := RawEquiv.rcns rtr
  have hnr := (Reaction.RawEquiv.isNorm_iff $ he.rel h hr).mp hn
  have hw := rtr.rawWF.direct.wfNormDeps nr i r hr
  simp [Set.subset_def, Set.mem_union] at hw
  rw [(he.rel h hr).deps] at hj
  cases (hw hnr j hj)
  case inl hw => exact Or.inl hw
  case inr hw =>
    apply Or.inr
    obtain ⟨i', ri', h₁, h₂⟩ := hw
    simp [nestedPortIDs, Set.finite.mem_to_finset]
    have hrip := Raw.Reactor.isAncestorOf_preserves_wf (Raw.Reactor.isAncestorOf.nested h₁) rtr.rawWF
    let rip := Reactor.fromRaw ri' hrip
    exists rip
    apply And.intro
    case h.left =>
      simp [Finmap.values_def]
      exists i'
      exact nest_mem_raw_iff.mpr h₁
    case h.right =>
      simp [ports', Raw.Reactor.ports', ports] at h₂ ⊢
      exact h₂

-- This constraint constrains the anti/-dependencies of `rtr`'s mutations, such that:
-- 1. their dependencies can only be input ports of `rtr`
-- 2. their antidependencies can only be output ports of `rtr` or input ports of reactors
--    nested directly in `rtr`
theorem wfMutDeps {rtr : Reactor ι υ} {m : Reaction ι υ} (r : Port.Role) (h : m ∈ rtr.muts.values) : 
  (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (m.deps Role.out ⊆ (rtr.ports' Role.out).ids ∪ rtr.nestedPortIDs Role.in) := by
  simp only [muts, Finmap.filter'_mem_values] at h
  obtain ⟨i, h, hm⟩ := h
  obtain ⟨mr, hr⟩ := rcns_has_raw h
  have he := RawEquiv.rcns rtr
  have hq := he.rel h hr
  have hrm := (Reaction.RawEquiv.isMut_iff hq).mp hm
  have hw := rtr.rawWF.direct.wfMutDeps mr i hr hrm
  obtain ⟨h₁, h₂⟩ := hw
  clear hw
  apply And.intro
  case left =>
    rw [hq.deps]
    simp [ports', ports, roles, Raw.Reactor.ports'] at h₁ ⊢
    exact h₁
  case right =>
    clear h₁
    simp [Set.subset_def, Set.mem_union] at h₂
    simp [Finset.subset_iff]  
    rw [hq.deps]
    intro j hj
    cases (h₂ j hj)
    case inl h => exact Or.inl h
    case inr h =>
      apply Or.inr
      obtain ⟨i', ri', h₁, h₂⟩ := h
      simp [nestedPortIDs, Set.finite.mem_to_finset]
      have hrip := Raw.Reactor.isAncestorOf_preserves_wf (Raw.Reactor.isAncestorOf.nested h₁) rtr.rawWF
      let rip := Reactor.fromRaw ri' hrip
      exists rip
      apply And.intro
      case h.left =>
        simp [Finmap.values_def]
        exists i'
        exact nest_mem_raw_iff.mpr h₁
      case h.right =>
        simp [ports', Raw.Reactor.ports', ports] at h₂ ⊢
        exact h₂

-- This constraint forces the priorities of mutations in a reactor to be greater than any of its normal reactions.
theorem mutsBeforeNorms {rtr : Reactor ι υ} {iₙ iₘ : ι} (hn : iₙ ∈ rtr.norms.ids) (hm : iₘ ∈ rtr.muts.ids) : 
  rtr.prios.lt iₘ iₙ := by
  have h := rtr.rawWF.direct.mutsBeforeNorms iₙ iₘ
  simp only [muts, norms, Finmap.filter'_mem_ids] at hn hm
  obtain ⟨hr₁, hm₁⟩ := hn.choose_spec
  obtain ⟨hr₂, hm₂⟩ := hm.choose_spec
  have hi₁ := (rcns_has_raw hr₁).choose_spec
  have hi₂ := (rcns_has_raw hr₂).choose_spec
  have he := RawEquiv.rcns rtr
  have hmr₁ := (Reaction.RawEquiv.isNorm_iff $ he.rel hr₁ hi₁).mp hm₁
  have hmr₂ := (Reaction.RawEquiv.isMut_iff  $ he.rel hr₂ hi₂).mp hm₂
  exact h _ _ hi₁ hmr₁ hi₂ hmr₂

-- This constraint forces the priorities of all mutations in a reactor to be comparable,
-- i.e. they form a linear order.
theorem mutsLinearOrder {rtr : Reactor ι υ} {i₁ i₂ : ι} (h₁ : i₁ ∈ rtr.muts.ids) (h₂ : i₂ ∈ rtr.muts.ids) : 
  rtr.prios.le i₁ i₂ ∨ rtr.prios.le i₂ i₁ := by
  have h := rtr.rawWF.direct.mutsLinearOrder i₁ i₂
  simp only [muts, Finmap.filter'_mem_ids] at h₁ h₂
  obtain ⟨hr₁, hm₁⟩ := h₁.choose_spec
  obtain ⟨hr₂, hm₂⟩ := h₂.choose_spec
  have hi₁ := (rcns_has_raw hr₁).choose_spec
  have hi₂ := (rcns_has_raw hr₂).choose_spec
  have he := RawEquiv.rcns rtr
  have hmr₁ := (Reaction.RawEquiv.isMut_iff $ he.rel hr₁ hi₁).mp hm₁
  have hmr₂ := (Reaction.RawEquiv.isMut_iff $ he.rel hr₂ hi₂).mp hm₂
  exact h _ _ hi₁ hi₂ hmr₁ hmr₂

-- A `Lineage` for a given ID `i` in the context of a reactor `σ` is a 
-- structure that traces a path through the nested reactors of `σ` that lead
-- to the component identified by `i`.
-- 
-- A `Lineage` captures two important aspects:
-- 
-- 1. The non-recursive constructors (`rtr`, `rcn`, `prt` and `stv`) tell us
-- what kind of component is identified by `i`.
-- 2. The recursive `nest` constructor captures all of the reactors `σ'` that
-- need to be traversed from the root reactor `σ` to arrive at the immediate
-- parent of `i`.
--
-- We use this structure to define ID-uniqueness (`uniqueIDs`) in reactors as
-- well as hierarchy accessors in Components>Reactor>Hierarchy.lean.
inductive Lineage : Reactor ι υ → ι → Type _ 
  | rtr {σ i} : i ∈ σ.nest.ids  → Lineage σ i
  | rcn {σ i} : i ∈ σ.rcns.ids  → Lineage σ i
  | prt {σ i} : i ∈ σ.ports.ids → Lineage σ i
  | act {σ i} : i ∈ σ.acts.ids  → Lineage σ i
  | stv {σ i} : i ∈ σ.state.ids → Lineage σ i
  | nest {σ : Reactor ι υ} σ' {i} i' : (Lineage σ' i) → (σ.nest i' = some σ') → Lineage σ i

-- TODO (maybe): Merge this into the proof of `uniqueIDs` if possible.
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unfold.20where
private def Lineage.toRaw {σ : Reactor ι υ} {i} : (Lineage σ i) → Raw.Reactor.Lineage σ.raw i
  | Lineage.prt h => Raw.Reactor.Lineage.prt σ.raw i h
  | Lineage.act h => Raw.Reactor.Lineage.act σ.raw i h
  | Lineage.stv h => Raw.Reactor.Lineage.stv σ.raw i h
  | Lineage.rcn h => Raw.Reactor.Lineage.rcn σ.raw i $ ((RawEquiv.rcns σ).eqIDs i).mp h
  | Lineage.rtr h => Raw.Reactor.Lineage.rtr σ.raw i $ ((RawEquiv.nest σ).eqIDs i).mp h
  | Lineage.nest _ i' l hn => Raw.Reactor.Lineage.nest σ.raw i i' (toRaw l) (nest_mem_raw_iff.mp hn)

-- Any component in a reactor that is addressable by an ID has a unique ID.
-- We define this property in terms of `Lineage`s, since a components is
-- addressable by an ID in a reactor iff it has a lineage in that reactor
-- (by construction of `Lineage`).
theorem uniqueIDs {σ : Reactor ι υ} {i} (l₁ l₂ : Lineage σ i) : l₁ = l₂ := by
  have h := σ.rawWF.direct.uniqueIDs l₁.toRaw l₂.toRaw
  induction l₁
  case nest _ σ₂ _ _ _ _ hi =>
    cases l₂ 
    case nest σ' _ _ _ =>
      simp [Lineage.toRaw] at h
      have hσ : σ₂ = σ' := by apply Reactor.raw_ext_iff.mpr; exact h.left
      subst hσ
      simp [h.right.left]
      exact hi _ $ eq_of_heq h.right.right
    all_goals { contradiction }
  all_goals { cases l₂ <;> simp [Lineage.toRaw] at * }

end Reactor