import ReactorModel.Components.Reaction

open Port

protected inductive Raw.Reactor 
  | mk 
    (ports : ID ⇉ Port )
    (acts :  ID ⇉ Time.Tag ⇉ Value)
    (state : ID ⇉ Value)
    (rcns :  ID ⇉ Reaction)
    (nest :  ID → Option Raw.Reactor)

namespace Raw.Reactor

-- These definitions give us the projections that would usually be generated for a structure.
def ports : Raw.Reactor → ID ⇉ Port               | mk p _ _ _ _ => p
def acts :  Raw.Reactor → ID ⇉ Time.Tag ⇉ Value   | mk _ a _ _ _ => a
def state : Raw.Reactor → ID ⇉ Value              | mk _ _ s _ _ => s 
def rcns :  Raw.Reactor → ID ⇉ Reaction           | mk _ _ _ r _ => r
def nest :  Raw.Reactor → ID → Option Raw.Reactor | mk _ _ _ _ n => n

noncomputable def norms (rtr : Raw.Reactor) : ID ⇉ Reaction :=
  rtr.rcns.filter' (Reaction.isNorm)

noncomputable def muts (rtr : Raw.Reactor) : ID ⇉ Reaction :=
  rtr.rcns.filter' (Reaction.isMut)  

noncomputable def ports' (rtr : Raw.Reactor) (r : Port.Role) : ID ⇉ Port := 
  rtr.ports.filter' (·.role = r)

noncomputable def portVals (rtr : Raw.Reactor) (r : Port.Role) : ID ⇉ Value := 
  (rtr.ports' r).map Port.val

def nestedPortIDs (rtr : Raw.Reactor) (r : Port.Role) : Set ID :=
  { i | ∃ j n, rtr.nest j = some n ∧ i ∈ (n.ports' r).ids }

inductive Lineage : Raw.Reactor → ID → Type _ 
  | rtr σ i : σ.nest i ≠ none → Lineage σ i
  | rcn σ i : i ∈ σ.rcns.ids  → Lineage σ i
  | prt σ i : i ∈ σ.ports.ids → Lineage σ i
  | act σ i : i ∈ σ.acts.ids  → Lineage σ i
  | stv σ i : i ∈ σ.state.ids → Lineage σ i
  | nest {σ rtr i j} : (Lineage rtr i) → (σ.nest j = some rtr) → Lineage σ i

inductive rcnsNeedTotalOrder (rtr : Raw.Reactor) (rcn₁ rcn₂ : Reaction) 
  | impure {i₁ i₂} : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (¬rcn₁.isPure) → (¬rcn₂.isPure) → rcnsNeedTotalOrder rtr rcn₁ rcn₂
  | output {i₁ i₂} : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.deps .out ∩ rcn₂.deps .out).nonempty → rcnsNeedTotalOrder rtr rcn₁ rcn₂
  | muts   {i₁ i₂} : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.isMut) → (rcn₂.isMut) → rcnsNeedTotalOrder rtr rcn₁ rcn₂

theorem ext_iff {rtr₁ rtr₂ : Raw.Reactor} : 
  rtr₁ = rtr₂ ↔ 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts ∧ 
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns = rtr₂.rcns ∧ 
  rtr₁.nest  = rtr₂.nest := by
  constructor
  case mp =>
    intro h
    cases rtr₁
    cases rtr₂
    simp [h]
  case mpr =>
    intro h
    simp [ports, state, rcns, acts, nest] at h
    cases rtr₁
    cases rtr₂
    simp [h]

end Raw.Reactor