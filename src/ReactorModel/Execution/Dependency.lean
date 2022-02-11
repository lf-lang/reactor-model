import ReactorModel.Components

variable {ι υ} [Value υ]

open Port

inductive Dependency (σ : Reactor ι υ) : ι → ι → Prop
  | internal (i₁ i₂) {iᵣ rtr rcn₁ rcn₂} : 
    (hc₁ : σ &[i₁]= iᵣ) → 
    (hc₂ : σ &[i₂]= iᵣ) →
    (hr : σ *[Cmp.rtr, iᵣ]= rtr) →
    (hr₁ : rtr.rcns i₁ = some rcn₁) →
    (hr₂ : rtr.rcns i₂ = some rcn₂) →
    (hi : rcn₁.prio > rcn₂.prio) → 
    Dependency σ i₁ i₂
  | external (i₁ i₂ : ι) {iₚ rcn₁ rcn₂} :
    (hr₁ : σ *[Cmp.rcn, i₁]= rcn₁) → 
    (hr₂ : σ *[Cmp.rcn, i₂]= rcn₂) → 
    (hp₁ : iₚ ∈ rcn₁.deps Role.out) → 
    (hp₂ : iₚ ∈ rcn₂.deps Role.in) → 
    Dependency σ i₁ i₂
  | trans (i₁ i₂ i₃) : Dependency σ i₁ i₂ → Dependency σ i₂ i₃ → Dependency σ i₁ i₃

notation i₁ " >[" σ "] " i₂ => Dependency σ i₁ i₂

def Reactor.dependencies (σ : Reactor ι υ) (rcn : ι) : Set ι := { rcn' | rcn' >[σ] rcn }