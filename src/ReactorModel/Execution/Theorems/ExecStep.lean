import ReactorModel.Execution.Theorems.Apply

open Classical ReactorType Execution State

namespace Execution.Step.Exec

variable [Indexable α] {s₁ : State α}

def rcn :                  (s₁ ↓ₑ s₂) → ID                               | mk (rcn := r) .. => r
def applied :              (s₁ ↓ₑ s₂) → State α                          | mk (s₂ := s) .. => s
theorem allows_rcn :   (e : s₁ ↓ₑ s₂) → Allows s₁ e.rcn                  | mk a .. => a
theorem triggers_rcn : (e : s₁ ↓ₑ s₂) → Triggers s₁ e.rcn                | mk _ t _ => t
theorem apply :        (e : s₁ ↓ₑ s₂) → s₁ -[s₁.output e.rcn]→ e.applied | mk _ _ a => a
theorem dst_eq :       (e : s₁ ↓ₑ s₂) → s₂ = e.applied.record e.rcn      | .mk .. => rfl

theorem preserves_tag (e : s₁ ↓ₑ s₂) : s₁.tag = s₂.tag := by
  simp [e.dst_eq, State.record_preserves_tag, e.apply.preserves_tag]

theorem equiv (e : s₁ ↓ₑ s₂) : s₁.rtr ≈ s₂.rtr := by
  simp [e.dst_eq, State.record_preserves_rtr, e.apply.equiv]

theorem progress_eq (e : s₁ ↓ₑ s₂) : s₂.progress = s₁.progress.insert e.rcn := by 
  simp [e.dst_eq, State.record_progress_eq, e.apply.preserves_progress]

end Execution.Step.Exec