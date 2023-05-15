import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.Reactor

open ReactorType Execution State

namespace Execution.Step.Time

variable [Indexable α] {s₁ : State α} in section

theorem closed :         (e : s₁ ↓ₜ s₂) → Closed s₁                                 | mk c .. => c
theorem next_tag :       (e : s₁ ↓ₜ s₂) → NextTag s₁ s₂.tag                         | mk _ n _ => n
theorem refreshed :      (e : s₁ ↓ₜ s₂) → Refresh s₁.rtr s₂.rtr (s₁.actions s₂.tag) | mk _ _ r => r
theorem progress_empty : (e : s₁ ↓ₜ s₂) → s₂.progress = ∅                           | mk .. => rfl
theorem events_eq :      (e : s₁ ↓ₜ s₂) → s₂.events = s₁.events                     | mk .. => rfl

theorem tag_lt (e : s₁ ↓ₜ s₂) : s₁.tag < s₂.tag := 
  e.next_tag.bound

theorem tag_ne (e : s₁ ↓ₜ s₂) : s₁.tag ≠ s₂.tag := 
  ne_of_lt e.tag_lt

theorem equiv (e : s₁ ↓ₜ s₂) : s₁.rtr ≈ s₂.rtr := 
  e.refreshed.equiv

end

variable [Proper α] {s : State α}

theorem deterministic (e₁ : s ↓ₜ s₁) (e₂ : s ↓ₜ s₂) : s₁ = s₂ := by
  have hn := e₁.next_tag.deterministic e₂.next_tag
  have hr := hn ▸ e₁.refreshed |>.deterministic e₂.refreshed
  ext1 <;> simp [hn, hr, e₁.progress_empty, e₂.progress_empty, e₁.events_eq, e₂.events_eq]

end Execution.Step.Time