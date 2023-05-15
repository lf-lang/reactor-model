import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.Grouped.Instantaneous
import ReactorModel.Execution.Theorems.Nontrivial

open ReactorType

namespace Execution.Grouped

variable [Indexable α]

inductive Step (s₁ s₂ : State α)
  | inst : (s₁ ↓ᵢ| s₂) → Step s₁ s₂
  | time : (s₁ ↓ₜ s₂) → Step s₁ s₂

namespace Step

variable {s₁ s₂ : State α}

theorem deterministic (e₁ : Step s s₁) (e₂ : Step s s₂) : s₁ = s₂ := by
  sorry

instance : Coe (s₁ ↓ᵢ| s₂) (Step s₁ s₂) where
  coe := inst

instance : Coe (s₁ ↓ₜ s₂) (Step s₁ s₂) where
  coe := time

end Step

inductive Steps : State α → State α → Type 
  | refl : Steps s s
  | step : (Step s₁ s₂) → (Steps s₂ s₃) → Steps s₁ s₃ 

namespace Steps

theorem tag_lt {s₁ : State α} (e : Steps s₁ s₂) : s₁.tag < s₂.tag := by
  sorry

theorem deterministic {s₁ s₂ : State α} (e₁ : Steps s s₁) (e₂ : Steps s s₂) (n : s.Nontrivial)
    (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) : s₁ = s₂ := by
  induction e₁ <;> cases e₂
  case refl.refl => rfl
  case step.step e₁ _ hi _ e₂ e₂' => 
    exact hi (e₁.deterministic e₂ ▸ e₂') sorry ht hp
  all_goals cases ‹Step _ _›
  case refl.step.time e' e =>
    have := e.tag_lt
    sorry -- s.tag < tl₂.tag
  case step.refl.time e' _ e =>
    have := e.tag_lt
    sorry -- tl₂.tag < s.tag
  case refl.step.inst =>
    sorry -- s.progress ⊂ tl₂.progress 
  case step.refl.inst =>
    sorry -- tl₂.progress ⊂ s.progress 

end Execution.Grouped.Steps