import ReactorModel.Determinism.ExecutionStep
import ReactorModel.Determinism.Trivial

open Classical

namespace Execution

variable [ReactorType.Practical α] {s s₁ s₂ : State α}

theorem tag_le {s₁ s₂ : State α} (e : s₁ ⇓* s₂) : s₁.tag ≤ s₂.tag := by
  induction e with
  | refl        => exact le_refl _
  | step e _ hi => exact le_trans e.tag_le hi

theorem seq_progress_ssubset_or_tag_lt [State.Nontrivial s₁] : 
    (s₁ ⇓ s₂) → (s₂ ⇓* s₃) → (s₁.progress ⊂ s₃.progress) ∨ (s₁.tag < s₃.tag)
  | e₁₂,        step e e' => .inr $ lt_of_lt_of_le (e₁₂.seq_tag_lt e) e'.tag_le
  | .close e,   refl      => .inl $ e.progress_ssubset
  | .advance a, refl      => .inr $ a.tag_lt

theorem nontrivial_deterministic {s s₁ s₂ : State α} [nontriv : State.Nontrivial s]
    (e₁ : s ⇓* s₁) (e₂ : s ⇓* s₂) (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) : 
    s₁ = s₂ := by
  induction e₁ generalizing s₂ nontriv <;> cases e₂
  case refl.refl => rfl
  case step.step e₁ _ hi _ e₂ e₂' =>
    have := e₁.preserves_nontrivial -- TODO: Make this work via type class inference.
    exact hi (e₁.deterministic e₂ ▸ e₂') ht hp
  all_goals
    have e := ‹_ ⇓ _›; have e' := ‹_ ⇓* _›
    have := e.preserves_nontrivial
    exact match seq_progress_ssubset_or_tag_lt e e' with
    | .inl h => absurd hp (Set.ssubset_ne $ by simp_all) 
    | .inr h => absurd ht $ ne_of_lt (by simp_all)

-- TODO: This theorem can be proven over non-`Finite` but `LawfulUpdatable`, `Proper` reactors. 
theorem deterministic : 
    (s ⇓* s₁) → (s ⇓* s₂) → (s₁.tag = s₂.tag) → (s₁.progress = s₂.progress) → s₁ = s₂ := 
  if h : State.Nontrivial s 
  then nontrivial_deterministic
  else fun e₁ e₂ ht _ => e₁.trivial_deterministic h e₂ ht
  
end Execution