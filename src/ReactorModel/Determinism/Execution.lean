import ReactorModel.Determinism.ExecutionStep

theorem Execution.tag_le (e : s₁ ⇓* s₂) : s₁.ctx.tag ≤ s₂.ctx.tag := by
  induction e with
  | refl => simp
  | step h _ hi => exact le_trans h.tag_le hi

theorem Execution.seq_currentProcessedRcns_ssubset_or_tag_lt : (s₁ ⇓ s₂) → (s₂ ⇓* s₃) → 
    (s₁.ctx.currentProcessedRcns ⊂ s₃.ctx.currentProcessedRcns) ∨ (s₁.ctx.tag < s₃.ctx.tag)
  | e₁₂,        .step e e' => .inr $ lt_of_lt_of_le (e₁₂.seq_tag_lt e) e'.tag_le
  | .close e,   .refl      => .inl $ e.currentProcessedRcns_ssubset
  | .advance a, .refl      => .inr $ a.tag_lt

protected theorem Execution.deterministic : (s ⇓* s₁) → (s ⇓* s₂) → 
    (s₁.ctx.tag = s₂.ctx.tag) → (s₁.ctx.currentProcessedRcns = s₂.ctx.currentProcessedRcns) → 
    s₁ = s₂ := by
  intro he₁ he₂ ht hc
  induction he₁ <;> cases he₂ 
  case refl.refl => rfl
  case step.step h₁ₘ₁ _ hi _ h₁ₘ₂ hₘ₂₂ => 
    rw [Execution.Step.deterministic h₁ₘ₁ h₁ₘ₂] at hi
    exact hi hₘ₂₂ ht hc
  case step.refl h₂₃ _ h₁₂ => 
    match seq_currentProcessedRcns_ssubset_or_tag_lt h₁₂ h₂₃ with
    | .inl h => exact absurd hc (Finset.ssubset_ne h).symm
    | .inr h => exact absurd ht (ne_of_lt h)
  case refl.step h₁₂ h₂₃ => 
    match seq_currentProcessedRcns_ssubset_or_tag_lt h₁₂ h₂₃ with
    | .inl h => exact absurd hc (Finset.ssubset_ne h)
    | .inr h => exact absurd ht (ne_of_lt h)