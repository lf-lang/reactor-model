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
  n.deps r ⊆ (rtr.ports' r).ids ∪ (rtr.nestedPortIDs r.opposite) :=
  sorry

theorem wfMutDeps {rtr : Reactor ι υ} {m : Reaction ι υ} (r : Ports.Role) (h : m ∈ rtr.muts.values) : 
  (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (m.deps Role.out ⊆ (rtr.ports' Role.out).ids ∪ rtr.nestedPortIDs Role.in) := 
  sorry

theorem mutsBeforeNorms {rtr : Reactor ι υ} {iₙ iₘ : ι} (hn : iₙ ∈ rtr.norms.ids) (hm : iₘ ∈ rtr.muts.ids) : 
  rtr.prios.lt iₘ iₙ := by
  have hw := rtr.rawWF.direct.mutsBeforeNorms iₙ iₘ
  suffices hg : (∃ n, rtr.raw.rcns iₙ = some n ∧ n.isNorm) ∧ (∃ m, rtr.raw.rcns iₘ = some m ∧ m.isMut) from hw hg.left hg.right
  clear hw
  -- simp [Finmap.ids_def] at hn hm 
  apply And.intro
  case left =>
    simp [norms, Finmap.filter'_mem_id] at hn
    obtain ⟨n, ⟨hl, hn⟩⟩ := hn
    sorry
  sorry
    -- Perhaps the whole toRaw thing is stupid, as you'd still need to prove `Raw.Reactor.rcns rtr.raw iₙ = some n` for that reaction n.

theorem mutsLinearOrder {rtr : Reactor ι υ} {i₁ i₂ : ι} (h₁ : i₁ ∈ rtr.muts.ids) (h₂ : i₂ ∈ rtr.muts.ids) : (rtr.prios.le i₁ i₂ ∨ rtr.prios.le i₂ i₁) := sorry 

inductive IDPath : Reactor ι υ → ι → Type _ 
  | rtr {σ i} : i ∈ σ.nest.ids  → IDPath σ i
  | rcn {σ i} : i ∈ σ.rcns.ids  → IDPath σ i
  | prt {σ i} : i ∈ σ.ports.ids → IDPath σ i
  | stv {σ i} : i ∈ σ.state.ids → IDPath σ i
  | nest {σ : Reactor ι υ} σ' {i} i' : (IDPath σ' i) → (σ.nest i' = some σ') → IDPath σ i

private def IDPath.toRaw {σ : Reactor ι υ} {i} : (IDPath σ i) → Raw.Reactor.IDPath σ.raw i
  | IDPath.prt h => Raw.Reactor.IDPath.prt σ.raw i h
  | IDPath.stv h => Raw.Reactor.IDPath.stv σ.raw i h
  | IDPath.rcn h => Raw.Reactor.IDPath.rcn σ.raw i $ ((rcns_rawEquiv σ).eqIDs i).mp h
  | IDPath.rtr h => Raw.Reactor.IDPath.rtr σ.raw i $ ((nest_rawEquiv σ).eqIDs i).mp h
  | IDPath.nest _ i' p hn => Raw.Reactor.IDPath.nest σ.raw i i' (toRaw p) (nest_rawEquiv' hn)

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
  
end Reactor