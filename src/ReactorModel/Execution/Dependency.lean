import ReactorModel.Components

open Port

inductive Dependency.Internal (σ : Reactor) : ID → ID → Prop
  | rcns {i₁ i₂ j rtr rcn₁ rcn₂} :
    (hc  : σ.obj? .rtr j = some rtr) →
    (hr₁ : rtr.rcns i₁ = some rcn₁) →
    (hr₂ : rtr.rcns i₂ = some rcn₂) →
    (hi  : rcn₁.prio > rcn₂.prio) →
    Internal σ i₁ i₂
  | mutNorm {iₘ iₙ j rtr} :
    (hc : σ.obj? .rtr j = some rtr) →
    (hm : iₘ ∈ rtr.muts.ids) →
    (hn : iₙ ∈ rtr.norms.ids) →
    Internal σ iₘ iₙ

inductive Dependency.External (σ : Reactor) : ID → ID → Prop
  | port {i₁ i₂ : ID} {iₚ rcn₁ rcn₂} :
    (hr₁ : σ.obj? .rcn i₁ = some rcn₁) →
    (hr₂ : σ.obj? .rcn i₂ = some rcn₂) →
    (hp₁ : iₚ ∈ rcn₁.deps Role.out) →
    (hp₂ : iₚ ∈ rcn₂.deps Role.in) →
    External σ i₁ i₂
  | «mut» {iₘ iᵣ j rtr₁ rtr₂} :
    (hc  : σ.obj? .rtr j = some rtr₁) →
    (hm  : iₘ ∈ rtr₁.muts.ids) → 
    (hr₁ : rtr₂ ∈ rtr₁.nest.values) →
    (hr₂ : iᵣ ∈ rtr₂.ids Cmp.rcn) → 
    External σ iₘ iₙ

open Dependency in
inductive Dependency (σ : Reactor) : ID → ID → Prop
  | internal {i₁ i₂} : Internal σ i₁ i₂ → Dependency σ i₁ i₂
  | external {i₁ i₂} : External σ i₁ i₂ → Dependency σ i₁ i₂
  | trans (i₁ i₂ i₃) : Dependency σ i₁ i₂ → Dependency σ i₂ i₃ → Dependency σ i₁ i₃

notation i₁:max " >[" σ "] " i₂:max => Dependency σ i₁ i₂

def Reactor.dependencies (σ : Reactor) (rcn : ID) : Set ID := { rcn' | rcn' >[σ] rcn }

def Reactor.Indep (σ : Reactor) (rcn₁ rcn₂ : ID) : Prop :=
  ¬(rcn₁ >[σ] rcn₂) ∧ ¬(rcn₂ >[σ] rcn₁)

notation i₁:max " >[" σ "]< " i₂:max => Reactor.Indep σ i₁ i₂

namespace Reactor.Indep

protected theorem symm : (rcn₁ >[σ]< rcn₂) → (rcn₂ >[σ]< rcn₁) :=
  And.symm

theorem ne_rtr_or_ne_out_deps : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (σ.con? .rcn i₁ ≠ σ.con? .rcn i₂) ∨ (rcn₁.deps Role.out ∩ rcn₂.deps Role.out) = ∅ := by
  intro h h₁ h₂ 
  by_contra hc
  have ⟨hc, hd⟩ := (not_or ..).mp hc
  simp [Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter] at hd hc
  sorry
  -- create an instance of Dependency rcn₁ rcn₂

  

end Reactor.Indep