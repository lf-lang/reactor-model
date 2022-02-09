import ReactorModel.Execution.Basic

variable {ι υ} [Value υ]

-- This file defines (and proves) determinism for the reactor model.
-- Determinism can be understood in multiple ways.
-- Primarily, we say the execution is deterministic if there is always ot most one timed
-- step that can be taken.
namespace Execution

theorem ChangeStep.eq_rcns {σ₁ σ₂ : Reactor ι υ} {c : Change ι υ} {g : Time.Tag} :
  σ₁ -[c, g]→ σ₂ → σ₁.rcns = σ₂.rcns := by
  intro h; cases h <;> simp only <;> (apply Reactor.Update.ne_cmp_and_ne_rtr_eq Cmp.rcn; assumption; all_goals { by_contra; contradiction })

theorem InstExecution.preserves_time {s₁ s₂ : State ι υ} :
  (s₁ ⇓ᵢ+ s₂) → s₁.ctx.time = s₂.ctx.time := by
  intro h
  induction h
  case single h => cases h <;> simp [Context.addCurrentExecuted_same_time]
  case trans s₁ s₂ _ h₁₂ h₂₃ hi => 
    have ht : s₁.ctx.time = s₂.ctx.time := by cases h₁₂ <;> simp [Context.addCurrentExecuted_same_time]
    simp [hi, ht]

theorem InstExecution.preserves_ctx_past_future {s₁ s₂ : State ι υ} :
  (s₁ ⇓ᵢ+ s₂) → ∀ g, g ≠ s₁.ctx.time → s₁.ctx.executedRcns g = s₂.ctx.executedRcns g := by
  intro h g hg
  induction h
  case single h => cases h <;> simp [Context.addCurrentExecuted, Finmap.update_ne]
  case trans s₁ s₂ _ he _ hi =>
    have hc : s₁.ctx.executedRcns g = s₂.ctx.executedRcns g := by cases he <;> simp [Context.addCurrentExecuted, Finmap.update_ne]
    rw [InstExecution.preserves_time $ single he] at hg
    simp [hc, hi hg]

-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
protected theorem InstExecution.deterministic {s s₁ s₂ : State ι υ} : 
  (s ⇓ᵢ+ s₁) → (s ⇓ᵢ+ s₂) → (s₁.ctx = s₂.ctx) → s₁ = s₂ := sorry

theorem StuckInstExecution.ctx_current_complete {s₁ s₂ : State ι υ} :
  (s₁ ⇓ᵢ| s₂) → s₂.ctx.executedRcns s₂.ctx.time = s₂.rtr.rcns.ids := by
  sorry -- This is probably non-trivial.

  
-- The set of reactions can change because of mutations.
-- However, these changes are deterministic.
--lemma networkChangeDeterministic {σ₁ σ₂ σ₁' σ₂' : Reactor ι υ}
--{ctx₁ ctx₂ ctx₁' ctx₂'  : Context ι} :
--  (σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁') →
--  (σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂') →
--  sameReactionExecuted ((σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁')) ((σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) →
--  sameReactionTopologyChanges ((σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁')) ((σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) :=
--  sorry

theorem StuckInstExecution.topology_convergent {s s₁ s₂ : State ι υ} :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.rtr.rcns = s₂.rtr.rcns := 
  sorry

theorem StuckInstExecution.eq_ctx {s s₁ s₂ : State ι υ} :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.ctx = s₂.ctx := by
  intro hs₁ hs₂
  apply Context.ext_iff.mpr; apply Finmap.ext
  intro g
  by_cases hg : g = s.ctx.time
  case pos => 
    have h₁ := hs₁.ctx_current_complete
    have h₂ := hs₂.ctx_current_complete
    simp only [←hs₁.exec.preserves_time, ←hs₂.exec.preserves_time, ←hg] at h₁ h₂
    simp only [h₁, h₂, StuckInstExecution.topology_convergent hs₁ hs₂]
  case neg => simp only [←hs₁.exec.preserves_ctx_past_future g hg, hs₂.exec.preserves_ctx_past_future g hg]

theorem StuckInstExecution.convergent {s s₁ s₂ : State ι υ} :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁ = s₂ :=
  λ hs₁ hs₂ => InstExecution.deterministic hs₁.exec hs₂.exec $ StuckInstExecution.eq_ctx hs₁ hs₂

protected theorem ExecutionStep.deterministic {s s₁ s₂ : State ι υ} : 
  (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂ := by
  intro he₁ he₂
  cases he₁ <;> cases he₂
  case instToStuck.instToStuck hs₁ hs₂ => 
    exact StuckInstExecution.convergent hs₁ hs₂
  case advanceTime.advanceTime g₁ hg₁ _ h₁ _ g₂ hg₂ _ h₂ => 
    simp [Reactor.eqWithClearedPortsUnique h₁ h₂, Context.advanceTime, State.isNextTag_unique hg₁ hg₂]
  case' instToStuck.advanceTime hs _ _ _ hr _, advanceTime.instToStuck _ _ _ _ hr _ hs => 
    cases hs.exec 
    case' single hi, trans hi _ =>
      cases hi <;> (
        have := mt (Finset.ext_iff.mp hr _).mpr <| (by assumption)
        have := Finmap.ids_def'.mpr ⟨_, Eq.symm (by assumption)⟩
        contradiction
      )
protected theorem Execution.deterministic {s s₁ s₂ : State ι υ} (hs₁ : s₁.instStuck) (hs₂ : s₂.instStuck) : 
  (s ⇓* s₁) → (s ⇓* s₂) → (s₁.ctx.time = s₂.ctx.time) → s₁ = s₂ := by
  intro he₁ he₂ ht
  induction he₁ <;> cases he₂ 
  case refl.refl => rfl
  case step.step hi _ _ _ => 
    have hi := hi hs₁
    sorry
  -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Collapse.20cases
  case refl.step h _ => sorry
  case step.refl h => 
    cases h <;> sorry
    -- TODO:
    -- instToStuck isnt possible, because we're already stuck.
    -- advanceTime advances time which contradicts ht

end Execution