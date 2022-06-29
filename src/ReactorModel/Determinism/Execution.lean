import ReactorModel.Determinism.InstExecution

open Classical

namespace Execution

theorem State.instComplete_to_inst_stuck : s.instComplete → ∀ s' rcn, ¬(s ⇓ᵢ[rcn] s') := by
  intro h s' _ he 
  have h' := Reactor.ids_mem_iff_contains.mpr he.rtr_contains_rcn
  rw [←h] at h'
  exact absurd h' he.rcn_unprocessed

theorem CompleteInstExecution.convergent_rcns :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.rtr.ids .rcn = s₂.rtr.ids .rcn
  | mk _ e₁ _, mk _ e₂ _ => by simp [Finset.ext_iff, Reactor.ids_mem_iff_contains, Reactor.contains_iff_obj?, ←e₁.preserves_rcns, e₂.preserves_rcns]

theorem CompleteInstExecution.convergent_ctx : 
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.ctx = s₂.ctx := by
  intro hc₁ hc₂
  ext
  intro g
  have hc₁₂ := hc₁.convergent_rcns hc₂
  cases hc₁ with | mk _ e₁ hc₁ => 
  cases hc₂ with | mk _ e₂ hc₂ => 
  by_cases hg : g = s.ctx.tag
  case pos => 
    have h₁ := hc₁ |> Option.some_inj.mpr
    have h₂ := hc₂ |> Option.some_inj.mpr
    rw [Context.currentProcessedRcns_def] at h₁ h₂
    simp only [←e₁.preserves_tag, ←e₂.preserves_tag, ←hg] at h₁ h₂
    simp only [h₁, h₂, hc₁₂]
  case neg => simp only [←e₁.preserves_ctx_past_future g hg, e₂.preserves_ctx_past_future g hg]

theorem CompleteInstExecution.deterministic : (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁ = s₂ :=
  λ hc₁ hc₂ => 
    match hc₁, hc₂ with 
    | mk _ e₁ _, mk _ e₂ _ => e₁.deterministic e₂ $ hc₁.convergent_ctx hc₂

end Execution

theorem Execution.Step.tag_monotone : (s₁ ⇓ s₂) → s₁.ctx.tag ≤ s₂.ctx.tag
  | completeInst (.mk _ e _) => le_of_eq e.preserves_tag
  | advanceTag hg .. => le_of_lt $ s₁.ctx.advanceTag_strictly_increasing (s₁.tag_lt_nextTag hg)

protected theorem Execution.Step.deterministic : 
  (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂ := by
  intro he₁ he₂
  cases he₁ <;> cases he₂
  case completeInst.completeInst hc₁ hc₂ => 
    exact CompleteInstExecution.deterministic hc₁ hc₂
  case advanceTag.advanceTag g₁ hg₁ _ h₁ _ g₂ hg₂ _ h₂ => 
    simp only [hg₁, Option.some_inj] at hg₂
    simp [clearingPorts_unique h₁ h₂, Context.advanceTag, hg₂]  
  case' completeInst.advanceTag hc _ _ _ hic _, advanceTag.completeInst _ _ _ hic _ hc => 
    cases hc with | mk _ e _ => 
    cases e; case' single hi, trans hi _ => exact False.elim $ impossible_case_aux hi hic
where
  impossible_case_aux {s₁ s₂ rcn} (hi : s₁ ⇓ᵢ[rcn] s₂) (hic : s₁.instComplete) : False := by
    exact absurd (Reactor.ids_mem_iff_contains.mpr hi.rtr_contains_rcn) $ mt (Finset.ext_iff.mp hic _).mpr <| hi.rcn_unprocessed

theorem Execution.tag_monotone : (s₁ ⇓* s₂) → s₁.ctx.tag ≤ s₂.ctx.tag := by
  intro h
  induction h with
  | refl => simp
  | step h _ hi => exact le_trans h.tag_monotone hi

protected theorem Execution.deterministic : 
  (s ⇓* s₁) → (s ⇓* s₂) → 
  (s₁.ctx.tag = s₂.ctx.tag) → (s₁.ctx.currentProcessedRcns = s₂.ctx.currentProcessedRcns) → 
  s₁ = s₂ := by
  intro he₁ he₂ ht hc
  induction he₁ <;> cases he₂ 
  case refl.refl => rfl
  case step.refl _ _ h₂₃ _ h₁₂ => exact False.elim $ impossible_case_aux hc.symm ht.symm h₁₂ h₂₃
  case refl.step _ _ h₁₂ h₂₃ => exact False.elim $ impossible_case_aux hc ht h₁₂ h₂₃
  case step.step s sₘ₁ s₁ h₁ₘ₁ hₘ₁₂ hi sₘ₂ h₁ₘ₂ hₘ₂₂ => 
    rw [Execution.Step.deterministic h₁ₘ₁ h₁ₘ₂] at hi
    sorry -- exact hi hc₁ hₘ₂₂ ht
where 
  impossible_case_aux {s₁ s₂ s₃ : State} :
    (s₁.ctx.currentProcessedRcns = s₃.ctx.currentProcessedRcns) →
    (s₁.ctx.tag = s₃.ctx.tag) →
    (s₁ ⇓ s₂) → (s₂ ⇓* s₃) → False := by
    intro hc ht h₁₂ h₂₃
    cases h₁₂
    case completeInst hi =>
      sorry
    case advanceTag hg _ _ => 
      have h := tag_monotone h₂₃
      rw [←ht] at h
      simp only at h
      have h' := s₁.ctx.advanceTag_strictly_increasing (s₁.tag_lt_nextTag hg)
      exact (lt_irrefl _ $ lt_of_le_of_lt h h').elim
