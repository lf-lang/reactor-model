import ReactorModel.Execution.Basic
variable {ι υ} [Value υ]

-- This file defines (and proves) determinism for the reactor model.
-- Determinism can be understood in multiple ways.
-- Primarily, we say the execution is deterministic if there is always ot most one timed
-- step that can be taken.
open Execution

lemma instExecMonotoneCtx {σ₁ σ₂ : Reactor ι υ} {ctx₁ ctx₂ : Context ι} :
 (σ₁, ctx₁) ⇓ᵢ (σ2, ctx₂) → ∃ i : ι, ctx₁.currentExecutedRcns.insert i = ctx₂.currentExecutedRcns :=
  sorry

lemma stuckAllExecuted  {σ : Reactor ι υ} {ctx : Context ι} :
 instantaneousStuck σ ctx ↔ σ.rcns.ids = ctx.currentExecutedRcns := 
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
    have Hexec₁ := stuckAllExecuted.1 Hstuck₁
    have Hexec₂ := stuckAllExecuted.1 Hstuck₂
    have Htopology := instantaneousConvergentTopology Hstep₁ Hstuck₁ Hstep₂ Hstuck₂
    rw [Htopology] at Hexec₁
    rewrite [Hexec₁] at Hexec₂
    have Htime₁ := instantaneousPreservesTime Hstep₁
    have Htime₂ := instantaneousPreservesTime Hstep₂
    rw [Htime₁] at Htime₂
    exact Context.currentIdentical Hexec₂ Htime₂

theorem Execution.timedDeterministic {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂  : Execution.Context ι} : 
   (σ, ctx) ⇓ (σ₁, ctx₁) ∧ (σ, ctx) ⇓ (σ₂, ctx₂) → σ₁ = σ₂ := by
  intros Hexec
  cases Hexec.1 with
   | instantaneousStep Hstep₁ Hstuck₁ => cases Hexec.2 with 
       | instantaneousStep Hstep₂ Hstuck₂ =>  
         apply instantaneousConvergent Hstep₁.1 Hstuck₁ Hstep₂.1 Hstuck₂
       | advanceTime Hgnext Hgshed Hgminfuture Hallrcns Hσequiv =>
         have Hmonotonectx := (instExecMonotoneCtx Hstep₁.1)
         rw [Hallrcns] at Hmonotonectx
         have Hcontra := exists.intro Hmonotonectx.
         -- should be: coq's discriminate
    | case advanceTime Hgnext₁ Hgshed₁ Hgminfuture₁ Hallrcns₁ Hσequiv₁ =>
        cases Hexec.2 with 
        | advanceTime Hgnext₂ Hgshed₂ Hgminfuture₂ Hallrcns₂ Hσequiv₂ =>
        exact (Reactor.eqWithClearedPortsUnique Hσequiv₁ Hσequiv₂)
        -- this does not use anything about the times... (as those are "encoded" in ctx₁ ctx₂)
        -- probably we need to add statement that ctx₁ = ctx₂ as well ()
        | instantaneousStep Hstep₂ Hstuck₂ =>
        sorry -- should be the same contradiction as above



        







        


         
   | advanceTime

  
  