import ReactorModel.Determinism.ExecutionStep
import ReactorModel.Determinism.Trivial

open Classical 

namespace Execution

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
    | .inr h => sorry -- WTF: absurd ht $ ne_of_lt h 

theorem deterministic : 
    (s ⇓* s₁) → (s ⇓* s₂) → (s₁.tag = s₂.tag) → (s₁.progress = s₂.progress) → s₁ = s₂ := 
  if h : State.Nontrivial s 
  then nontrivial_deterministic
  else fun e₁ e₂ ht _ => e₁.trivial_deterministic h e₂ ht
  
end Execution