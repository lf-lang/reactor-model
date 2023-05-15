import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.Grouped.Instantaneous
import ReactorModel.Execution.Theorems.Nontrivial

open ReactorType

namespace Execution.Grouped

inductive Step [Indexable α] (s₁ s₂ : State α)
  | inst : (s₁ ↓ᵢ| s₂) → Step s₁ s₂
  | time : (s₁ ↓ₜ s₂) → Step s₁ s₂

namespace Step

variable [Indexable α] {s₁ s₂ : State α}

theorem tag_le : (Step s₁ s₂) → s₁.tag ≤ s₂.tag
  | inst e => e.preserves_tag ▸ le_refl _
  | time e => le_of_lt e.tag_lt

instance : Coe (s₁ ↓ᵢ| s₂) (Step s₁ s₂) where
  coe := inst

instance : Coe (s₁ ↓ₜ s₂) (Step s₁ s₂) where
  coe := time

end Step

theorem Step.deterministic [Proper α] {s s₁ s₂ : State α} : (Step s s₁) → (Step s s₂) → s₁ = s₂
  | inst e₁, inst e₂                    => e₁.deterministic e₂
  | time e₁, time e₂                    => e₁.deterministic e₂
  | inst e₁, time e₂ | time e₂, inst e₁ => e₁.not_closed e₂.closed |>.elim

inductive Steps [Indexable α] : State α → State α → Type 
  | refl : Steps s s
  | step : (Step s₁ s₂) → (Steps s₂ s₃) → Steps s₁ s₃ 

namespace Steps

theorem tag_le [Indexable α] {s₁ s₂ : State α} (e : Steps s₁ s₂) : s₁.tag ≤ s₂.tag := by
  induction e
  case refl => rfl
  case step e _ hi => exact le_trans e.tag_le hi

theorem deterministic [Proper α] {s s₁ s₂ : State α} 
    (e₁ : Steps s s₁) (e₂ : Steps s s₂) (n : s.Nontrivial) (ht : s₁.tag = s₂.tag) 
    (hp : s₁.progress = s₂.progress) : s₁ = s₂ := by
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