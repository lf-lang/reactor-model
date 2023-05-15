import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.Grouped.Instantaneous

open ReactorType

namespace Execution.Grouped

variable [Indexable α]

inductive Tail : State α → State α → Type
  | none  : Tail s s
  | some : (s₁ ↓ᵢ+ s₂) → Tail s₁ s₂

namespace Tail

theorem preserves_tag {s₁ : State α} (e : Tail s₁ s₂) : s₁.tag = s₂.tag := by
  sorry

theorem deterministic {s₁ s₂ : State α} (e₁ : Tail s s₁) (e₂ : Tail s s₂) 
    (hp : s₁.progress = s₂.progress) : s₁ = s₂ := by
  sorry

end Execution.Grouped.Tail