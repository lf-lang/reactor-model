import ReactorModel.Execution.Basic
variable {ι υ} [Value υ]

-- This file defines (and proves) determinism for the reactor model.
-- Determinism can be understood in multiple ways.
-- Primarily, we say the execution is deterministic if there is always ot most one timed
-- step that can be taken.
open Execution

lemma stuckAllExecuted  {σ : Reactor ι υ} {ctx : Context ι} :
 instantaneousStuck σ ctx →  σ.rcns.ids = ctx.currentExecutedRcns := 
 sorry


-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
theorem instantaneousDeterministic {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂  : Context ι} : 
   (σ, ctx) ⇓ᵢ* (σ₁, ctx₁) ∧ (σ, ctx) ⇓ᵢ* (σ₂, ctx₂) → ctx₁ = ctx₂ → σ₁ = σ₂ := sorry

-- The set of reactions can change because of mutations.
-- However, these changes are deterministic.
--lemma networkChangeDeterministic {σ₁ σ₂ σ₁' σ₂' : Reactor ι υ}
--{ctx₁ ctx₂ ctx₁' ctx₂'  : Context ι} :
--  (σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁') →
--  (σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂') →
--  sameReactionExecuted ((σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁')) ((σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) →
--  sameReactionTopologyChanges ((σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁')) ((σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) :=
--  sorry
lemma instantaneousConvergentTopology {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂  : Context ι} :
    (σ, ctx) ⇓ᵢ* (σ₁, ctx₁) →
    instantaneousStuck σ₁ ctx₁ →
    (σ, ctx) ⇓ᵢ* (σ₂, ctx₂) →
    instantaneousStuck σ₂ ctx₂ →
    σ₁.rcns.ids = σ₂.rcns.ids := by 
    sorry -- will surely need networkChangeDeterministic (and that should be made to work, too)
--
lemma instantaneousPreservesTime {σ₁ σ₂ : Reactor ι υ} {ctx₁ ctx₂ : Context ι } :
  (σ₁, ctx₁) ⇓ᵢ* (σ₂, ctx₂) → ctx₁.time = ctx₂.time := sorry

lemma instantaneousConvergent {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂  : Context ι} :
    (σ, ctx) ⇓ᵢ* (σ₁, ctx₁) →
    instantaneousStuck σ₁ ctx₁ →
    (σ, ctx) ⇓ᵢ* (σ₂, ctx₂) →
    instantaneousStuck σ₂ ctx₂ →
    σ₁ = σ₂ := by
    intros Hstep₁ Hstuck₁ Hstep₂ Hstuck₂
    have Hsteps := And.intro Hstep₁ Hstep₂
    apply instantaneousDeterministic  Hsteps
    have Hexec₁ := stuckAllExecuted Hstuck₁
    have Hexec₂ := stuckAllExecuted Hstuck₂
    have Htopology := instantaneousConvergentTopology Hstep₁ Hstuck₁ Hstep₂ Hstuck₂
    rw [Htopology] at Hexec₁
    rewrite [Hexec₁] at Hexec₂
    have Htime₁ := instantaneousPreservesTime Hstep₁
    have Htime₂ := instantaneousPreservesTime Hstep₂
    rw [Htime₁] at Htime₂
    exact Context.currentIdentical Hexec₂ Htime₂

theorem Execution.timedDeterministic {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂  : Execution.Context ι} : 
   (σ, ctx) ⇓ (σ₁, ctx₁) ∧ (σ, ctx) ⇓ (σ₂, ctx₂) → σ₁ = σ₂ ∧ ctx₁ = ctx₂ := sorry

  