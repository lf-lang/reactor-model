import ReactorModel.Execution.Trace
import ReactorModel.Execution.Theorems.Grouped.Instantaneous

open ReactorType

namespace Execution.Grouped

variable [Indexable α]

inductive Steps : State α → State α → Type 
  | refl : Steps s s
  | step : (s₂ ↓ₜ s₃) → (s₁ ↓ᵢ| s₂) → (Steps s₃ s₄) → Steps s₁ s₄ 

namespace Steps

theorem tag_strictly_monotonic {s₁ : State α} (e : Steps s₁ s₂) : s₁.tag < s₂.tag := by
  sorry

theorem deterministic {s₁ s₂ : State α} (e₁ : Steps s s₁) (e₂ : Steps s s₂) 
    (ht : s₁.tag = s₂.tag) : s₁ = s₂ := by
  sorry

end Execution.Grouped.Steps