import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.State

open Classical ReactorType Execution State

namespace Execution.Step.Apply

variable [Indexable α] {s₁ : State α} {c : Change}

theorem preserves_tag (e : s₁ -[c]→ s₂) : s₁.tag = s₂.tag := by
  cases e <;> simp [schedule_preserves_tag]

theorem preserves_progress (e : s₁ -[c]→ s₂) : s₁.progress = s₂.progress := by 
  cases e <;> simp [schedule_preserves_progress]

theorem equiv (e : s₁ -[c]→ s₂) : s₁.rtr ≈ s₂.rtr := by
  cases e
  case «mut» => exact .refl _
  case act => simp [schedule_preserves_rtr]; exact .refl _
  all_goals exact LawfulUpdate.equiv ‹_›

end Execution.Step.Apply

theorem Execution.Step.Apply.deterministic [Readable α] {s s₁ s₂ : State α} {c : Change} 
    (e₁ : s -[c]→ s₁) (e₂ : s -[c]→ s₂) : s₁ = s₂ := by
  cases e₁ <;> cases e₂ <;> simp <;> exact LawfulUpdate.unique ‹_› ‹_›

namespace Execution.Step.Apply.RTC

variable [Indexable α] {s₁ : State α} {cs : List Change}

theorem preserves_tag (e : s₁ -[cs]→ s₂) : s₁.tag = s₂.tag := by 
  induction e
  case refl => rfl
  case trans e _ hi => exact e.preserves_tag ▸ hi

theorem preserves_progress (e : s₁ -[cs]→ s₂) : s₁.progress = s₂.progress := by 
  induction e
  case refl => rfl
  case trans e _ hi => exact e.preserves_progress ▸ hi

theorem equiv (e : s₁ -[cs]→ s₂) : s₁.rtr ≈ s₂.rtr := by
  induction e
  case refl => exact .refl _
  case trans e _ hi => exact Equivalent.trans e.equiv hi

end Execution.Step.Apply.RTC

theorem Execution.Step.Apply.RTC.deterministic [Readable α] {s s₁ s₂ : State α} {cs : List Change}
    (e₁ : s -[cs]→ s₁) (e₂ : s -[cs]→ s₂) : s₁ = s₂ := by
  induction e₁ generalizing s₂ <;> cases e₂
  case refl.refl => rfl
  case trans.trans e₁ _ hi _ e₂ e₂' => exact hi $ (e₁.deterministic e₂) ▸ e₂'