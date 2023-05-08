import ReactorModel.Execution.Trace
open ReactorType

namespace Execution.Grouped

variable [Indexable α]

inductive Tail : State α → State α → Type
  | nil  : Tail s s
  | time : (s₁ ↓ₜ s₂) → Tail s₁ s₂

end Execution.Grouped