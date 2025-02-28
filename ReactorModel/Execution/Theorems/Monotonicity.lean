import ReactorModel.Execution.Theorems.Step.Basic

open Classical Reactor

namespace Execution

variable [Proper α] {s₁ s₂ : State α}

-- Property (1) on page 10 of https://www.informatik.uni-bremen.de/agbs/jp/papers/trs_script.pdf.
theorem tag_le (e : s₁ ⇓ s₂) : s₁.tag ≤ s₂.tag := by
  induction e
  case refl           => rfl
  case trans e₁ e₂ ih => exact e₁.tag_le.trans ih
