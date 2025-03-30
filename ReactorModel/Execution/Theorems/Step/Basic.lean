import ReactorModel.Execution.Theorems.Step.Skip
import ReactorModel.Execution.Theorems.Step.Exec
import ReactorModel.Execution.Theorems.Step.Time

open Reactor Execution

variable [Hierarchical α] {s₁ s₂ : State α}

theorem Execution.Step.tag_le : (Step s₁ s₂) → s₁.tag ≤ s₂.tag
  | .skip e | .exec e => le_of_eq e.preserves_tag
  | .time e           => le_of_lt e.tag_lt
