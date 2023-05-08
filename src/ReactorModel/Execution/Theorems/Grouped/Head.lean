import ReactorModel.Execution.Trace
import ReactorModel.Execution.Theorems.Grouped.Instantaneous

open ReactorType

namespace Execution.Grouped

variable [Indexable α]

inductive Head : State α → State α → Type
  | nil  : Head s s
  | inst : (s₁ ↓ᵢ| s₂) → Head s₁ s₂

namespace Head

theorem preserves_tag {s₁ : State α} (e : Head s₁ s₂) : s₁.tag = s₂.tag := by
  sorry

theorem deterministic {s₁ s₂ : State α} (e₁ : Head s s₁) (e₂ : Head s s₂) 
    (hp : s₁.progress = s₂.progress) : s₁ = s₂ := by
  sorry

end Execution.Grouped.Head