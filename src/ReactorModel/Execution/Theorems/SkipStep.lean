import ReactorModel.Execution.Basic

open Classical ReactorType Execution State

namespace Execution.Step.Skip

variable [Indexable α] {s₁ : State α}

def rcn :                      (s₁ ↓ₛ s₂) → ID                   | .mk (rcn := rcn) .. => rcn
theorem allows_rcn :       (e : s₁ ↓ₛ s₂) → Allows s₁ e.rcn      | .mk a _ => a
theorem not_triggers_rcn : (e : s₁ ↓ₛ s₂) → ¬Triggers s₁ e.rcn   | .mk _ t => t
theorem dst_eq :           (e : s₁ ↓ₛ s₂) → s₂ = s₁.record e.rcn | .mk .. => rfl

theorem preserves_tag (e : s₁ ↓ₛ s₂) : s₁.tag = s₂.tag := by
  simp [e.dst_eq, State.record_preserves_tag]

theorem equiv (e : s₁ ↓ₛ s₂) : s₁.rtr ≈ s₂.rtr := by
  simp [e.dst_eq, State.record_preserves_rtr]
  exact .refl _

theorem progress_eq (e : s₁ ↓ₛ s₂) : s₂.progress = s₁.progress.insert e.rcn := by 
  simp [e.dst_eq, State.record_progress_eq]

end Execution.Step.Skip