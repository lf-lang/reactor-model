import ReactorModel.Components.Reactor.Projections

-- This file will contain theorems proving the WF-properties of `Reactor`
-- for "proper"-land.
-- Note, we only need to lift those properties which are "about" reactors
-- and IDs, i.e. those which would be part of the reactor-type, if we
-- could define it as a structure.
-- The other properties are all present in the redefinitions of and change,
-- reaction.

variable {ι υ} [ID ι] [Value υ]

namespace Reactor

theorem wfRoles (rtr : Reactor ι υ) : rtr.roles.ids = rtr.ports.ids := rtr.rawWF.direct.wfRoles

theorem wfNormDeps {rtr : Reactor ι υ} {n : Reaction ι υ} (r : Ports.Role) (h : n ∈ rtr.norms.values) : n.deps r ⊆ (rtr.ports' r).ids ∪ (rtr.nestedPorts r.opposite) := sorry

-- theorem wfMutDeps {rtr : Reactor ι υ} {m : Reaction ι υ} (r : Ports.Role) (h : m ∈ rtr.muts.values) : (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (↑(m.deps Role.out) ⊆ ↑(rtr.ports' Role.out).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' Role.in).ids})

theorem mutsBeforeNorms {rtr : Reactor ι υ} {iₙ iₘ : ι} (hn : iₙ ∈ rtr.norms.ids) (hm : iₘ ∈ rtr.muts.ids) : rtr.prios.lt iₘ iₙ := by
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

inductive IDPath : Reactor ι υ → ι → Cmp → Type _ 
  | rtr {σ i} : i ∈ σ.nest.ids  → IDPath σ i Cmp.rtr
  | rcn {σ i} : i ∈ σ.rcns.ids  → IDPath σ i Cmp.rcn
  | prt {σ i} : i ∈ σ.ports.ids → IDPath σ i Cmp.prt
  | stv {σ i} : i ∈ σ.state.ids → IDPath σ i Cmp.stv
  | nest {σ σ' : Reactor ι υ} {cmp i} (i') : (IDPath σ' i cmp) → (σ.nest i' = some σ') → IDPath σ i cmp

structure idUniqueness (σ : Reactor ι υ) : Prop where
  external : ∀ {i cmp} (p₁ p₂ : IDPath σ i cmp), p₁ = p₂
  internal : ∀ {i cmp₁ cmp₂} (p₁ : IDPath σ i cmp₁) (p₂ : IDPath σ i cmp₂), cmp₁ = cmp₂ 

private def IDPath.toRaw {σ : Reactor ι υ} {i} : {cmp : Cmp} → (IDPath σ i cmp) → Raw.Reactor.IDPath σ.raw i cmp
  | Cmp.prt, IDPath.prt h => Raw.Reactor.IDPath.prt σ.raw i h
  | Cmp.stv, IDPath.stv h => Raw.Reactor.IDPath.stv σ.raw i h
  | Cmp.rcn, IDPath.rcn h => Raw.Reactor.IDPath.rcn σ.raw i $ ((rcns_rawEquiv σ).eqIDs i).mp h
  | Cmp.rtr, IDPath.rtr h => Raw.Reactor.IDPath.rtr σ.raw i $ ((nest_rawEquiv σ).eqIDs i).mp h
  | cmp, IDPath.nest i' p hn => Raw.Reactor.IDPath.nest σ.raw cmp i i' (toRaw p) (nest_rawEquiv' hn)

private theorem IDPath.eq_if_toRaw_eq {σ : Reactor ι υ} {i cmp} {p₁ p₂ : IDPath σ i cmp} (h : p₁.toRaw = p₂.toRaw) : p₁ = p₂ := by
  induction p₁ <;> cases p₂ <;> simp [toRaw] at *
  case nest.nest i₁ p₁ he₁ σ' i₂ he₂ p₂ hi =>
    sorry

theorem uniqueIDs (σ : Reactor ι υ) : idUniqueness σ := {
  external := λ p₁ p₂ => IDPath.eq_if_toRaw_eq (σ.rawWF.direct.uniqueIDs.external p₁.toRaw p₂.toRaw)
  internal := λ p₁ p₂ => σ.rawWF.direct.uniqueIDs.internal p₁.toRaw p₂.toRaw
}

end Reactor