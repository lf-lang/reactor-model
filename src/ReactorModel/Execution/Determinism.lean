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
  instStuck σ ctx ↔ σ.rcns.ids = ctx.currentExecutedRcns := 
  sorry

-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
theorem instantaneousDeterministic {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx' : Context ι} : 
   (σ, ctx) ⇓ᵢ+ (σ₁, ctx') → (σ, ctx) ⇓ᵢ+ (σ₂, ctx') → σ₁ = σ₂ := sorry

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
    (σ, ctx) ⇓ᵢ| (σ₁, ctx₁) →
    (σ, ctx) ⇓ᵢ| (σ₂, ctx₂) →
    σ₁.rcns.ids = σ₂.rcns.ids := by 
    sorry -- will surely need networkChangeDeterministic (and that should be made to work, too)
--
lemma instantaneousPreservesTime {σ₁ σ₂ : Reactor ι υ} {ctx₁ ctx₂ : Context ι } :
  (σ₁, ctx₁) ⇓ᵢ+ (σ₂, ctx₂) → ctx₁.time = ctx₂.time := sorry

lemma instConvergent {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂  : Context ι} :
  (σ, ctx) ⇓ᵢ| (σ₁, ctx₁) → (σ, ctx) ⇓ᵢ| (σ₂, ctx₂) → σ₁ = σ₂ := by
    intro ⟨Hstep₁, Hstuck₁⟩ ⟨Hstep₂, Hstuck₂⟩
    sorry
    /-apply instantaneousDeterministic Hstep₁ Hstep₂
    have Hexec₁ := stuckAllExecuted.1 Hstuck₁
    have Hexec₂ := stuckAllExecuted.1 Hstuck₂
    have Htopology := instantaneousConvergentTopology Hstep₁ Hstuck₁ Hstep₂ Hstuck₂
    rw [Htopology] at Hexec₁
    rewrite [Hexec₁] at Hexec₂
    have Htime₁ := instantaneousPreservesTime Hstep₁
    have Htime₂ := instantaneousPreservesTime Hstep₂
    rw [Htime₁] at Htime₂
    exact Context.currentIdentical Hexec₂ Htime₂-/

theorem Execution.timedDeterministic {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂ : Context ι} : 
  (σ, ctx) ⇓ (σ₁, ctx₁) → (σ, ctx) ⇓ (σ₂, ctx₂) → σ₁ = σ₂ := by
  intro he₁ he₂
  cases he₁
  case instToStuck hs₁ =>
    cases he₂
    case instToStuck hs₂ => exact instConvergent hs₁ hs₂
    case advanceTime hg hgm hl hr hp => 
      exfalso
      cases hs₁.exec
      case h.single hi =>
        cases hi 
        case execReaction =>
          sorry

      have Hmonotonectx := (instExecMonotoneCtx hs₁.exec)
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
-/



  
-- TODO: What assumptions are required?
--       E.g. we probably need to require a total order on reactions' priorities.
-- theorem Execution.deterministic {σ σ₁ : Reactor ι υ} {ctx ctx₁ : Execution.Context ι}
  
namespace Execution

theorem ChangeStep.eq_prios {σ₁ σ₂ : Reactor ι υ} {c : Change ι υ} {g : Time.Tag} :
  σ₁ -[c, g]→ σ₂ → σ₁.prios = σ₂.prios := by
  intro h; cases h <;> apply Reactor.Update.eq_prios <;> assumption

theorem ChangeStep.eq_rcns {σ₁ σ₂ : Reactor ι υ} {c : Change ι υ} {g : Time.Tag} :
  σ₁ -[c, g]→ σ₂ → σ₁.rcns = σ₂.rcns := by
  intro h; cases h <;> (apply Reactor.Update.ne_cmp_and_ne_rtr_eq Cmp.rcn; assumption; all_goals { by_contra; contradiction })

theorem InstantaneousStep.eq_prios {σ₁ σ₂ : Reactor ι υ} {ctx₁ ctx₂ : Context ι} {i : ι} :
  (σ₁, ctx₁) ⇓ᵢ[i₁] (σ₂, ctx₂) → σ₁.prios = σ₂.prios := by
  intro h
  cases h
  case skipReaction => rfl
  case execReaction rcn _ _ _ _ h =>
    generalize hcs : rcn (σ₁.inputForRcn rcn ctx₁.time) = cs
    rw [hcs] at h
    induction h
    case nil => rfl
    case cons σ₁ σ₂ σ₃ hd tl hhd htl hi hr hp ht =>
      have hr' := ChangeStep.eq_rcns hhd
      simp only [Reactor.predecessors, ←hr', ←(ChangeStep.eq_prios hhd)] at hi
      have hi' := hi hr hp
      sorry -- ...

  

namespace Determinism

theorem instantaneous {σ₁ σ₂ σ₃ : Reactor ι υ} {ctx₁ ctx₂ ctx₃ : Context ι} {i₁ i₂ : ι} :
  (σ₁, ctx₁) ⇓ᵢ[i₁] (σ₂, ctx₂) → (σ₂, ctx₂) ⇓ᵢ[i₂] (σ₃, ctx₃) → ¬(σ₁.prios.lt i₁ i₂) := by
  sorry

end Determinism

end Execution
