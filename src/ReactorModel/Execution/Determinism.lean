import ReactorModel.Execution.Basic

open Classical

-- This file defines (and proves) determinism for the reactor model.
-- Determinism can be understood in multiple ways.
-- Primarily, we say the execution is deterministic if there is always ot most one timed
-- step that can be taken.
namespace Execution

theorem InstExecution.first_step {s₁ s₂ : State} (he : s₁ ⇓ᵢ+ s₂) : ∃ sₘ, s₁ ⇓ᵢ sₘ := by 
  cases he; case' single h, trans s₂ h _ => exact ⟨s₂, h⟩

theorem InstExecution.preserves_time {s₁ s₂ : State} :
  (s₁ ⇓ᵢ+ s₂) → s₁.ctx.time = s₂.ctx.time := by
  intro h
  induction h
  case single h => cases h <;> simp [Context.addCurrentExecuted_same_time]
  case trans s₁ s₂ _ h₁₂ h₂₃ hi => 
    have ht : s₁.ctx.time = s₂.ctx.time := by cases h₁₂ <;> simp [Context.addCurrentExecuted_same_time]
    simp [hi, ht]

theorem InstExecution.preserves_ctx_past_future {s₁ s₂ : State} :
  (s₁ ⇓ᵢ+ s₂) → ∀ g, g ≠ s₁.ctx.time → s₁.ctx.executedRcns g = s₂.ctx.executedRcns g := by
  intro h g hg
  induction h
  case single h => cases h <;> simp [Context.addCurrentExecuted, Finmap.update_ne]
  case trans s₁ s₂ _ he _ hi =>
    have hc : s₁.ctx.executedRcns g = s₂.ctx.executedRcns g := by cases he <;> simp [Context.addCurrentExecuted, Finmap.update_ne]
    rw [InstExecution.preserves_time $ single he] at hg
    simp [hc, hi hg]

-- Note: this only talks about the top-level reactions, not the nested ones.
theorem InstExecution.convergent_rcns {s s₁ s₂ : State} :
  (s ⇓ᵢ+ s₁) → (s ⇓ᵢ+ s₂) → s₁.rtr.rcns = s₂.rtr.rcns := by
  sorry

-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
protected theorem InstExecution.deterministic {s s₁ s₂ : State} : 
  (s ⇓ᵢ+ s₁) → (s ⇓ᵢ+ s₂) → (s₁.ctx = s₂.ctx) → s₁ = s₂ := by
  intro he₁ he₂ hc
  sorry

theorem State.instComplete_to_inst_stuck {s : State} :
  s.instComplete → ∀ s', ¬(s ⇓ᵢ s') := by
  intro h s' he
  cases he
  case' execReaction hi _ hm _ _, skipReaction hi _ hm _ =>
  have h' := Finmap.ids_def'.mpr ⟨_, Eq.symm hi⟩
  rw [←h] at h'
  contradiction

-- The set of reactions can change because of mutations.
-- However, these changes are deterministic.
--lemma networkChangeDeterministic {σ₁ σ₂ σ₁' σ₂' : Reactor}
--{ctx₁ ctx₂ ctx₁' ctx₂'  : Context} :
--  (σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁') →
--  (σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂') →
--  sameReactionExecuted ((σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁')) ((σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) →
--  sameReactionTopologyChanges ((σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁')) ((σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) :=
--  sorry

theorem CompleteInstExecution.convergent_ctx {s s₁ s₂ : State} :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.ctx = s₂.ctx := by
  intro hc₁ hc₂
  apply Context.ext_iff.mpr; apply Finmap.ext
  intro g
  by_cases hg : g = s.ctx.time
  case pos => 
    have h₁ := hc₁.complete |> Option.some_inj.mpr
    have h₂ := hc₂.complete |> Option.some_inj.mpr
    rw [Context.currentExecutedRcns_def] at h₁ h₂
    simp only [←hc₁.exec.preserves_time, ←hc₂.exec.preserves_time, ←hg] at h₁ h₂
    simp only [h₁, h₂, InstExecution.convergent_rcns hc₁.exec hc₂.exec]
  case neg => simp only [←hc₁.exec.preserves_ctx_past_future g hg, hc₂.exec.preserves_ctx_past_future g hg]

theorem CompleteInstExecution.convergent {s s₁ s₂ : State} :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁ = s₂ :=
  λ hc₁ hc₂ => InstExecution.deterministic hc₁.exec hc₂.exec $ CompleteInstExecution.convergent_ctx hc₁ hc₂

end Execution

theorem Execution.Step.time_monotone {s₁ s₂ : State} : 
  (s₁ ⇓ s₂) → s₁.ctx.time ≤ s₂.ctx.time := by
  intro h
  cases h
  case completeInst h => exact le_of_eq h.exec.preserves_time
  case advanceTime hg _ _ => exact le_of_lt $ s₁.ctx.advanceTime_strictly_increasing _ hg.lower

protected theorem Execution.Step.deterministic {s s₁ s₂ : State} : 
  (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂ := by
  intro he₁ he₂
  cases he₁ <;> cases he₂
  case completeInst.completeInst hc₁ hc₂ => 
    exact CompleteInstExecution.convergent hc₁ hc₂
  case advanceTime.advanceTime g₁ hg₁ _ h₁ _ g₂ hg₂ _ h₂ => 
    simp [Reactor.eqWithClearedPortsUnique h₁ h₂, Context.advanceTime, State.isNextTag_unique hg₁ hg₂]
  case' completeInst.advanceTime hc _ _ _ hr _, advanceTime.completeInst _ _ _ hr _ hc => 
    cases hc.exec 
    case' single hi, trans hi _ =>
      cases hi <;> (
        have := mt (Finset.ext_iff.mp hr _).mpr <| (by assumption)
        have := Finmap.ids_def'.mpr ⟨_, Eq.symm (by assumption)⟩
        contradiction
      )

theorem Execution.time_monotone {s₁ s₂ : State} : 
  (s₁ ⇓* s₂) → s₁.ctx.time ≤ s₂.ctx.time := by
  intro h
  induction h 
  case refl => simp
  case step h _ hi => exact le_trans h.time_monotone hi

protected theorem Execution.deterministic {s s₁ s₂ : State} (hc₁ : s₁.instComplete) (hc₂ : s₂.instComplete) : 
  (s ⇓* s₁) → (s ⇓* s₂) → (s₁.ctx.time = s₂.ctx.time) → s₁ = s₂ := by
  intro he₁ he₂ ht
  induction he₁ <;> cases he₂ 
  case refl.refl => rfl
  case step.refl _ _ h₂₃ _ h₁₂ => exact False.elim $ impossible_case_aux hc₂ (Eq.symm ht) h₁₂ h₂₃
  case refl.step _ _ h₁₂ h₂₃ => exact False.elim $ impossible_case_aux hc₁ ht h₁₂ h₂₃
  case step.step s sₘ₁ s₁ h₁ₘ₁ hₘ₁₂ hi sₘ₂ h₁ₘ₂ hₘ₂₂ => 
    rw [Execution.Step.deterministic h₁ₘ₁ h₁ₘ₂] at hi
    exact hi hc₁ hₘ₂₂ ht
where 
  impossible_case_aux {s₁ s₂ s₃ : State} (hc : s₁.instComplete) (ht : s₁.ctx.time = s₃.ctx.time) :
    (s₁ ⇓ s₂) → (s₂ ⇓* s₃) → False := by
    intro h₁₂ h₂₃
    cases h₁₂
    case completeInst hi =>
      have ⟨sₘ, _⟩ := hi.exec.first_step
      have := (State.instComplete_to_inst_stuck hc) sₘ
      contradiction
    case advanceTime g hg _ _ => 
      have h := time_monotone h₂₃
      rw [←ht] at h
      simp only at h
      have h' := s₁.ctx.advanceTime_strictly_increasing g hg.lower
      have h'' := lt_of_le_of_lt h h'
      have := lt_irrefl _ h''
      contradiction