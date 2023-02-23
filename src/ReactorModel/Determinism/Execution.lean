import ReactorModel.Determinism.ExecutionStep

open Classical 

namespace Execution

theorem trivial_rtr_eq [State.Trivial s₁] : (s₁ ⇓* s₂) → s₁.rtr = s₂.rtr
  | refl      => rfl
  | step e e' => 
    have := e.preserves_Trivial -- TODO: Make this work via type class inference.
    e.trivial_rtr_eq ▸ e'.trivial_rtr_eq

theorem trivial_ctx_eq [State.Trivial s₁] : (s₁ ⇓* s₂) →
  s₂.ctx = (s₁.ctx.mark $ s₁.rtr.scheduledTags.filter fun g => s₁.tag < g ∧ g ≤ s₂.tag) :=
    sorry

theorem trivial_deterministic [trivial : State.Trivial s] 
    (e₁ : s ⇓* s₁) (e₂ : s ⇓* s₂) (ht : s₁.tag = s₂.tag) : s₁ = s₂ := by
  ext1
  · exact e₁.trivial_rtr_eq ▸ e₂.trivial_rtr_eq 
  · rw [e₁.trivial_ctx_eq, e₂.trivial_ctx_eq, ht]

theorem tag_le : (s₁ ⇓* s₂) → s₁.tag ≤ s₂.tag
  | refl      => le_refl _
  | step e e' => le_trans e.tag_le e'.tag_le

theorem seq_progress_ssubset_or_tag_lt [State.Nontrivial s₁] : 
    (s₁ ⇓ s₂) → (s₂ ⇓* s₃) → (s₁.progress ⊂ s₃.progress) ∨ (s₁.tag < s₃.tag)
  | e₁₂,        .step e e' => .inr $ lt_of_lt_of_le (e₁₂.seq_tag_lt e) e'.tag_le
  | .close e,   .refl      => .inl $ e.progress_ssubset
  | .advance a, .refl      => .inr $ a.tag_lt

theorem nontrivial_deterministic [State.Nontrivial s] :
    (s ⇓* s₁) → (s ⇓* s₂) → (s₁.tag = s₂.tag) → (s₁.progress = s₂.progress) → s₁ = s₂
  | refl, refl, _, _ => rfl
  | step e₁ e₁', step e₂ e₂', ht, hp => 
    have := e₂.preserves_Nontrivial -- TODO: Make this work via type class inference.
    nontrivial_deterministic (e₁.deterministic e₂ ▸ e₁') e₂' ht hp
  | refl, step e e', ht, hp | step e e', refl, ht, hp => 
    match seq_progress_ssubset_or_tag_lt e e' with
    | .inl h => absurd hp $ Finset.ssubset_ne (by simp_all) 
    | .inr h => absurd ht $ ne_of_lt h

theorem deterministic : 
    (s ⇓* s₁) → (s ⇓* s₂) → (s₁.tag = s₂.tag) → (s₁.progress = s₂.progress) → s₁ = s₂ := 
  if h : State.Nontrivial s 
  then nontrivial_deterministic
  else fun e₁ e₂ ht _ => trivial_deterministic e₁ e₂ ht (trivial := ⟨h⟩)
  
end Execution