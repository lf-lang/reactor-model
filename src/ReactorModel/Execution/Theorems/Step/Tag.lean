import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.Reactor
import ReactorModel.Execution.Theorems.State

open Reactor Execution State

namespace Execution.Step.Tag

variable [Hierarchical α] {s₁ : State α}

theorem closed :         (e : s₁ ↓ᵗ s₂) → Closed s₁                                  | mk c .. => c
theorem next_tag :       (e : s₁ ↓ᵗ s₂) → NextTag s₁ s₂.tag                          | mk _ n .. => n
theorem refreshed :      (e : s₁ ↓ᵗ s₂) → Refresh s₁.rtr s₂.rtr (s₁.logicals s₂.tag) | mk _ _ r .. => r
theorem tag_le_clock :   (e : s₁ ↓ᵗ s₂) → s₂.tag.time ≤ s₂.clock                     | mk _ _ _ t .. => t
theorem progress_empty : (e : s₁ ↓ᵗ s₂) → s₂.progress = ∅                            | mk .. => rfl
theorem events_eq :      (e : s₁ ↓ᵗ s₂) → s₂.events = s₁.events                      | mk .. => rfl

theorem tag_lt (e : s₁ ↓ᵗ s₂) : s₁.tag < s₂.tag := 
  e.next_tag.bound

theorem tag_ne (e : s₁ ↓ᵗ s₂) : s₁.tag ≠ s₂.tag := 
  ne_of_lt e.tag_lt

theorem equiv (e : s₁ ↓ᵗ s₂) : s₁.rtr ≈ s₂.rtr := 
  e.refreshed.equiv

theorem preserves_nontrivial {e : s₁ ↓ᵗ s₂} (n : s₁.Nontrivial) : s₂.Nontrivial :=
  n.equiv e.equiv

theorem not_closed (e : s₁ ↓ᵗ s₂) (n : s₁.Nontrivial) : ¬s₂.Closed :=
  (·.progress_nonempty (e.preserves_nontrivial n) |>.ne_empty e.progress_empty)

theorem nonrepeatable (e₁ : s₁ ↓ᵗ s₂) (e₂ : s₂ ↓ᵗ s₃) (n : s₁.Nontrivial) : False :=
  e₁.not_closed n e₂.closed

end Execution.Step.Tag

theorem Execution.Step.Tag.deterministic [Proper α] {s s₁ s₂ : State α} 
    (e₁ : s ↓ᵗ s₁) (e₂ : s ↓ᵗ s₂) : s₁ ≈ s₂ := by
  have hn := e₁.next_tag.deterministic e₂.next_tag
  have hr := hn ▸ e₁.refreshed |>.deterministic e₂.refreshed
  constructor <;> simp [hn, hr, e₁.progress_empty, e₂.progress_empty, e₁.events_eq, e₂.events_eq]