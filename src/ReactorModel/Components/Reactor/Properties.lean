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
  (rtr.prios.le i₁ i₂ ∨ rtr.prios.le i₂ i₁) := by
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

inductive IDPath : Reactor ι υ → ι → Type _ 
  | rtr {σ i} : i ∈ σ.nest.ids  → IDPath σ i
  | rcn {σ i} : i ∈ σ.rcns.ids  → IDPath σ i
  | prt {σ i} : i ∈ σ.ports.ids → IDPath σ i
  | stv {σ i} : i ∈ σ.state.ids → IDPath σ i
  | nest {σ : Reactor ι υ} σ' {i} i' : (IDPath σ' i) → (σ.nest i' = some σ') → IDPath σ i

namespace IDPath

def cmp {σ : Reactor ι υ} {i} : IDPath σ i → Cmp
  | rtr _ => Cmp.rtr
  | rcn _ => Cmp.rcn
  | prt _ => Cmp.prt
  | stv _ => Cmp.stv
  | nest _ _ p _ => p.cmp

-- Returns the reactor that matches the last ID in the ID-path (along with the ID).
def last {σ : Reactor ι υ} {i} : IDPath σ i → (ι × Reactor ι υ)
  | rtr _ => (⊤, σ)
  | rcn _ => (⊤, σ)
  | prt _ => (⊤, σ)
  | stv _ => (⊤, σ)
  | nest σ' i' (rtr _ ) _ => (i', σ')
  | nest σ' i' (rcn _ ) _ => (i', σ')
  | nest σ' i' (prt _ ) _ => (i', σ')
  | nest σ' i' (stv _ ) _ => (i', σ')
  | nest _ _ p _ => last p

private def toRaw {σ : Reactor ι υ} {i} : (IDPath σ i) → Raw.Reactor.IDPath σ.raw i
  | IDPath.prt h => Raw.Reactor.IDPath.prt σ.raw i h
  | IDPath.stv h => Raw.Reactor.IDPath.stv σ.raw i h
  | IDPath.rcn h => Raw.Reactor.IDPath.rcn σ.raw i $ ((rcns_rawEquiv σ).eqIDs i).mp h
  | IDPath.rtr h => Raw.Reactor.IDPath.rtr σ.raw i $ ((nest_rawEquiv σ).eqIDs i).mp h
  | IDPath.nest _ i' p hn => Raw.Reactor.IDPath.nest σ.raw i i' (toRaw p) (nest_rawEquiv' hn)

end IDPath

theorem uniqueIDs {σ : Reactor ι υ} {i} (p₁ p₂ : IDPath σ i) : p₁ = p₂ := by
  have h := σ.rawWF.direct.uniqueIDs p₁.toRaw p₂.toRaw
  induction p₁
  case nest _ σ₂ _ _ _ _ hi =>
    cases p₂ 
    case nest σ' _ _ _ =>
      simp [IDPath.toRaw] at h
      have hσ : σ₂ = σ' := by ext; exact h.left
      subst hσ
      simp [h.right.left]
      exact hi _ $ eq_of_heq h.right.right
    all_goals { contradiction }
  all_goals { cases p₂ <;> simp [IDPath.toRaw] at * }

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Name.20structure.20constructor
-- TODO: Figure out how to make a "proper" constructor for `Reactor`.
--       This isn't trivial, as the properties above use constructs like `ports'`.  

end Reactor