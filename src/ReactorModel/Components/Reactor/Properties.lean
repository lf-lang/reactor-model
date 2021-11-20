import ReactorModel.Components.Reactor.Projections

-- This file will contain theorems proving the WF-properties of `Reactor`
-- for "proper"-land.
-- Note, we only need to lift those properties which are "about" reactors
-- and IDs, i.e. those which would be part of the reactor-type, if we
-- could define it as a structure.
-- The other properties are all present in the redefinitions of and change,
-- reaction.

open Ports

variable {ι υ} [ID ι] [Value υ]

namespace Reactor

theorem wfRoles (rtr : Reactor ι υ) : rtr.roles.ids = rtr.ports.ids := rtr.rawWF.direct.wfRoles

theorem wfNormDeps {rtr : Reactor ι υ} {n : Reaction ι υ} (r : Ports.Role) (h : n ∈ rtr.norms.values) : 
  n.deps r ⊆ (rtr.ports' r).ids ∪ rtr.nestedPortIDs r.opposite :=
  sorry

theorem wfMutDeps {rtr : Reactor ι υ} {m : Reaction ι υ} (r : Ports.Role) (h : m ∈ rtr.muts.values) : 
  (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (m.deps Role.out ⊆ (rtr.ports' Role.out).ids ∪ rtr.nestedPortIDs Role.in) := by
  simp only [muts, Finmap.filter'_mem_values] at h
  obtain ⟨i, h, hm⟩ := h
  obtain ⟨mr, hr⟩ := rcns_has_raw h
  have he := rcns_rawEquiv rtr
  have hq := he.rel h hr
  have hrm := (Reaction.rawEquiv_isMut_iff hq).mp hm
  have hw := rtr.rawWF.direct.wfMutDeps mr i hr hrm
  obtain ⟨h₁, h₂⟩ := hw
  clear hw
  apply And.intro
  case left =>
    clear h₂
    sorry
  case right =>
    clear h₁
    simp at h₂
    sorry  

theorem mutsBeforeNorms {rtr : Reactor ι υ} {iₙ iₘ : ι} (hn : iₙ ∈ rtr.norms.ids) (hm : iₘ ∈ rtr.muts.ids) : 
  rtr.prios.lt iₘ iₙ := by
  have h := rtr.rawWF.direct.mutsBeforeNorms iₙ iₘ
  simp only [muts, norms, Finmap.filter'_mem_ids] at hn hm
  obtain ⟨hr₁, hm₁⟩ := hn.choose_spec
  obtain ⟨hr₂, hm₂⟩ := hm.choose_spec
  have hi₁ := (rcns_has_raw hr₁).choose_spec
  have hi₂ := (rcns_has_raw hr₂).choose_spec
  have he := rcns_rawEquiv rtr
  have hmr₁ := (Reaction.rawEquiv_isNorm_iff $ he.rel hr₁ hi₁).mp hm₁
  have hmr₂ := (Reaction.rawEquiv_isMut_iff  $ he.rel hr₂ hi₂).mp hm₂
  exact h _ _ hi₁ hmr₁ hi₂ hmr₂

theorem mutsLinearOrder {rtr : Reactor ι υ} {i₁ i₂ : ι} (h₁ : i₁ ∈ rtr.muts.ids) (h₂ : i₂ ∈ rtr.muts.ids) : 
  rtr.prios.le i₁ i₂ ∨ rtr.prios.le i₂ i₁ := by
  have h := rtr.rawWF.direct.mutsLinearOrder i₁ i₂
  simp only [muts, Finmap.filter'_mem_ids] at h₁ h₂
  obtain ⟨hr₁, hm₁⟩ := h₁.choose_spec
  obtain ⟨hr₂, hm₂⟩ := h₂.choose_spec
  have hi₁ := (rcns_has_raw hr₁).choose_spec
  have hi₂ := (rcns_has_raw hr₂).choose_spec
  have he := rcns_rawEquiv rtr
  have hmr₁ := (Reaction.rawEquiv_isMut_iff $ he.rel hr₁ hi₁).mp hm₁
  have hmr₂ := (Reaction.rawEquiv_isMut_iff $ he.rel hr₂ hi₂).mp hm₂
  exact h _ _ hi₁ hi₂ hmr₁ hmr₂

inductive Lineage : Reactor ι υ → ι → Type _ 
  | rtr {σ i} : i ∈ σ.nest.ids  → Lineage σ i
  | rcn {σ i} : i ∈ σ.rcns.ids  → Lineage σ i
  | prt {σ i} : i ∈ σ.ports.ids → Lineage σ i
  | stv {σ i} : i ∈ σ.state.ids → Lineage σ i
  | nest {σ : Reactor ι υ} σ' {i} i' : (Lineage σ' i) → (σ.nest i' = some σ') → Lineage σ i

-- Returns the reactor that matches the last ID in the ID-path (along with the ID).
def Lineage.last {σ : Reactor ι υ} {i} : Lineage σ i → (ι × Reactor ι υ)
  | rtr _ => (⊤, σ)
  | rcn _ => (⊤, σ)
  | prt _ => (⊤, σ)
  | stv _ => (⊤, σ)
  | nest σ' i' (rtr _ ) _ => (i', σ')
  | nest σ' i' (rcn _ ) _ => (i', σ')
  | nest σ' i' (prt _ ) _ => (i', σ')
  | nest σ' i' (stv _ ) _ => (i', σ')
  | nest _ _ l _ => last l

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unfold.20where
theorem uniqueIDs {σ : Reactor ι υ} {i} (l₁ l₂ : Lineage σ i) : l₁ = l₂ := by
  have h := σ.rawWF.direct.uniqueIDs (toRaw l₁) (toRaw l₂)
  induction l₁
  case nest _ σ₂ _ _ _ _ hi =>
    cases l₂ 
    case nest σ' _ _ _ =>
      simp [toRaw] at h
      have hσ : σ₂ = σ' := by ext; exact h.left
      subst hσ
      simp [h.right.left]
      exact hi _ $ eq_of_heq h.right.right
    all_goals { contradiction }
  all_goals { cases l₂ <;> simp [toRaw] at * }
where
  toRaw {σ : Reactor ι υ} {i} : (Lineage σ i) → Raw.Reactor.Lineage σ.raw i
    | Lineage.prt h => Raw.Reactor.Lineage.prt σ.raw i h
    | Lineage.stv h => Raw.Reactor.Lineage.stv σ.raw i h
    | Lineage.rcn h => Raw.Reactor.Lineage.rcn σ.raw i $ ((rcns_rawEquiv σ).eqIDs i).mp h
    | Lineage.rtr h => Raw.Reactor.Lineage.rtr σ.raw i $ ((nest_rawEquiv σ).eqIDs i).mp h
    | Lineage.nest _ i' l hn => Raw.Reactor.Lineage.nest σ.raw i i' (toRaw l) (nest_rawEquiv' hn)

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Name.20structure.20constructor
-- TODO: Figure out how to make a "proper" constructor for `Reactor`.
--       This isn't trivial, as the properties above use constructs like `ports'`.  

end Reactor