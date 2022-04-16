import ReactorModel.Components

open Port

inductive Dependency.Internal (σ : Reactor) : ID → ID → Prop
  | rcns {i₁ i₂ j rtr rcn₁ rcn₂} :
    (hc  : σ *[Cmp.rtr:j]= rtr) →
    (hr₁ : rtr.rcns i₁ = some rcn₁) →
    (hr₂ : rtr.rcns i₂ = some rcn₂) →
    (hi  : rcn₁.prio > rcn₂.prio) →
    Internal σ i₁ i₂
  | mutNorm {iₘ iₙ j rtr} :
    (hc : σ *[Cmp.rtr:j]= rtr) →
    (hm : iₘ ∈ rtr.muts.ids) →
    (hn : iₙ ∈ rtr.norms.ids) →
    Internal σ iₘ iₙ

inductive Dependency.External (σ : Reactor) : ID → ID → Prop
  | port {i₁ i₂ : ID} {iₚ rcn₁ rcn₂} :
    (hr₁ : σ *[Cmp.rcn:i₁]= rcn₁) →
    (hr₂ : σ *[Cmp.rcn:i₂]= rcn₂) →
    (hp₁ : iₚ ∈ rcn₁.deps Role.out) →
    (hp₂ : iₚ ∈ rcn₂.deps Role.in) →
    External σ i₁ i₂
  | «mut» {iₘ iᵣ j rtr₁ rtr₂} :
    (hc  : σ *[Cmp.rtr:j]= rtr₁) → 
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

theorem Reactor.Indep.symm : (rcn₁ >[σ]< rcn₂) → (rcn₂ >[σ]< rcn₁) :=
  And.symm
