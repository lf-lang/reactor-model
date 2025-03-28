import ReactorModel.Execution.Theorems.Step.Skip
import ReactorModel.Execution.Theorems.Step.Exec
import ReactorModel.Execution.Theorems.Step.Time

open Classical Reactor Execution State

variable [Hierarchical α] {s₁ s₂ : State α}

namespace Execution.Step

theorem preserves_nontrivial (n : s₁.Nontrivial) : (Step s₁ s₂) → s₂.Nontrivial
  | skip e | exec e | time e => e.preserves_nontrivial n

theorem tag_le : (Step s₁ s₂) → s₁.tag ≤ s₂.tag
  | .skip e | .exec e => le_of_eq e.preserves_tag
  | .time e           => le_of_lt e.tag_lt
