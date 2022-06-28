import ReactorModel.Components.Reaction

protected inductive Raw.Reactor 
  | mk 
    (ports : ID ⇉ Port)
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

noncomputable def ports' (rtr : Raw.Reactor) (k : Kind) : ID ⇉ Port :=
  rtr.ports.filter' (·.kind = k)

noncomputable def norms (rtr : Raw.Reactor) : ID ⇉ Reaction :=
  rtr.rcns.filter' (Reaction.isNorm)

noncomputable def muts (rtr : Raw.Reactor) : ID ⇉ Reaction :=
  rtr.rcns.filter' (Reaction.isMut)  

def nestedPortIDs (rtr : Raw.Reactor) (k : Kind) : Set ID :=
  { i | ∃ j n, (rtr.nest j = some n) ∧ (i ∈ (n.ports' k).ids) }

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

inductive Raw.Orderable (rtr : Raw.Reactor) (rcn₁ rcn₂ : Reaction) 
  | impure : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (¬rcn₁.isPure) → (¬rcn₂.isPure)            → Orderable rtr rcn₁ rcn₂
  | output : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.deps .out ∩ rcn₂.deps .out).nonempty → Orderable rtr rcn₁ rcn₂
  | muts   : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.isMut) → (rcn₂.isMut)                → Orderable rtr rcn₁ rcn₂

protected inductive Raw.Lineage : Raw.Reactor → ID → Type _ 
  | rtr : σ.nest i ≠ none → Raw.Lineage σ i
  | rcn : i ∈ σ.rcns.ids  → Raw.Lineage σ i
  | act : i ∈ σ.acts.ids  → Raw.Lineage σ i
  | stv : i ∈ σ.state.ids → Raw.Lineage σ i
  | prt : i ∈ σ.ports.ids → Raw.Lineage σ i
  | nest : (Raw.Lineage rtr i) → (σ.nest j = some rtr) → Raw.Lineage σ i