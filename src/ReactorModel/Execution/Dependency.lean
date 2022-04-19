import ReactorModel.Components

open Port

inductive Dependency.Internal (σ : Reactor) : ID → ID → Prop
  | rcns :
    (hc  : σ.con? .rcn i₁ = σ.con? .rcn i₂) →
    (hr₁ : σ.obj? .rcn i₁ = some rcn₁) →
    (hr₂ : σ.obj? .rcn i₂ = some rcn₂) →
    (hi  : rcn₁.prio > rcn₂.prio) →
    Internal σ i₁ i₂
  | mutNorm :
    -- TODO: It might be nicer here to change the structure to 
    --       be akin to the `rcns` constructor.
    (hc : σ.obj? .rtr j = some rtr) →
    (hm : iₘ ∈ rtr.muts.ids) →
    (hn : iₙ ∈ rtr.norms.ids) →
    Internal σ iₘ iₙ

inductive Dependency.External (σ : Reactor) : ID → ID → Prop
  | port {i₁ i₂ : ID} :
    (hr₁ : σ.obj? .rcn i₁ = some rcn₁) →
    (hr₂ : σ.obj? .rcn i₂ = some rcn₂) →
    (hp₁ : iₚ ∈ rcn₁.deps .out) →
    (hp₂ : iₚ ∈ rcn₂.deps Role.in) →
    External σ i₁ i₂
  | «mut» :
    (hc  : σ.obj? .rtr j = some rtr₁) →
    (hm  : iₘ ∈ rtr₁.muts.ids) → 
    (hr₁ : rtr₂ ∈ rtr₁.nest.values) →
    (hr₂ : iᵣ ∈ rtr₂.ids Cmp.rcn) → 
    External σ iₘ iₙ

open Dependency in
inductive Dependency (σ : Reactor) : ID → ID → Prop
  | internal : Internal σ i₁ i₂ → Dependency σ i₁ i₂
  | external : External σ i₁ i₂ → Dependency σ i₁ i₂
  | trans : Dependency σ i₁ i₂ → Dependency σ i₂ i₃ → Dependency σ i₁ i₃

notation i₁:max " >[" σ "] " i₂:max => Dependency σ i₁ i₂

def Reactor.dependencies (σ : Reactor) (rcn : ID) : Set ID := { rcn' | rcn' >[σ] rcn }

def Reactor.Indep (σ : Reactor) (rcn₁ rcn₂ : ID) : Prop :=
  ¬(rcn₁ >[σ] rcn₂) ∧ ¬(rcn₂ >[σ] rcn₁)

notation i₁:max " >[" σ "]< " i₂:max => Reactor.Indep σ i₁ i₂

namespace Reactor.Indep

protected theorem symm : (rcn₁ >[σ]< rcn₂) → (rcn₂ >[σ]< rcn₁) :=
  And.symm

protected theorem irreflexive : ¬(rcn >[σ]< rcn) := by
  sorry

-- Corollary of `irreflexive`.
theorem ne_rcns : (rcn₁ >[σ]< rcn₂) → rcn₁ ≠ rcn₂ := by
  intro h hc
  rw [hc] at h
  exact h.irreflexive

theorem ne_rtr_or_ne_out_deps : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (σ.con? .rcn i₁ ≠ σ.con? .rcn i₂) ∨ (rcn₁.deps .out ∩ rcn₂.deps .out) = ∅ := by
  intro h h₁ h₂ 
  by_contra hc
  have ⟨hc, hd⟩ := (not_or ..).mp hc
  simp at hc
  have ⟨rtr₁, hc₁, hr₁⟩ := Reactor.obj?_to_con?_and_cmp? h₁
  have ⟨rtr₂, hc₂, hr₂⟩ := Reactor.obj?_to_con?_and_cmp? h₂
  have H : rtr₁ = rtr₂ := sorry -- consequence of hc
  rw [←H] at hr₂
  cases rtr₁.obj.rcnsTotalOrder (.output hr₁ hr₂ h.ne_rcns hd)
  case h.inl hp => exact absurd (.internal $ .rcns hc.symm h₂ h₁ hp) h.right
  case h.inr hp => exact absurd (.internal $ .rcns hc      h₁ h₂ hp) h.left  

theorem ne_out_deps :
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (rcn₁.deps .out ∩ rcn₂.deps .out) = ∅ := by
  sorry -- Corollary of ne_rtr_or_ne_out_deps

theorem no_chain : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (rcn₁.deps .out ∩ rcn₂.deps Role.in) = ∅ :=
  sorry

theorem ne_rtr_or_pure : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (σ.con? .rcn i₁ ≠ σ.con? .rcn i₂) ∨ rcn₁.isPure ∨ rcn₂.isPure := by
  intro h h₁ h₂ 
  by_contra hc
  have ⟨hc, hd⟩ := (not_or ..).mp hc
  simp [not_or] at hd hc
  have ⟨rtr₁, hc₁, hr₁⟩ := Reactor.obj?_to_con?_and_cmp? h₁
  have ⟨rtr₂, hc₂, hr₂⟩ := Reactor.obj?_to_con?_and_cmp? h₂
  have H : rtr₁ = rtr₂ := sorry -- consequence of hc
  rw [←H] at hr₂
  cases rtr₁.obj.rcnsTotalOrder (.impure hr₁ hr₂ h.ne_rcns hd.left hd.right)
  case h.inl hp => exact absurd (.internal $ .rcns hc.symm h₂ h₁ hp) h.right
  case h.inr hp => exact absurd (.internal $ .rcns hc      h₁ h₂ hp) h.left  

end Reactor.Indep