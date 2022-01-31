import ReactorModel.Execution.Basic
variable {ι υ} [Value υ]

-- This file defines (and proves) determinism for the reactor model.
-- Determinism can be understood in multiple ways.
-- Primarily, we say the execution is deterministic if there is always ot most one timed
-- step that can be taken.

lemma Execution.instantaneousConvergent {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂  : Execution.Context ι} :
    (σ, ctx) ⇓ᵢ* (σ₁, ctx₁) →
    Execution.instantaneousStuck σ₁ ctx₁ →
    (σ, ctx) ⇓ᵢ* (σ₂, ctx₂) →
    Execution.instantaneousStuck σ₂ ctx₂ →
    σ₁ = σ₂ ∧ ctx₁ = ctx₂ := sorry


theorem Execution.timedDeterministic {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂  : Execution.Context ι} : 
   (σ, ctx) ⇓ (σ₁, ctx₁) ∧ (σ, ctx) ⇓ (σ₂, ctx₂) → σ₁ = σ₂ ∧ ctx₁ = ctx₂ := sorry

  