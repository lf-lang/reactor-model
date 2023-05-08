import ReactorModel.Execution.Theorems.Trivial 
import ReactorModel.Execution.Theorems.Grouped

open Classical ReactorType

namespace Execution

variable [Proper α] {s : State α}

theorem deterministic 
    (e₁ : s ⇓ s₁) (e₂ : s ⇓ s₂) (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) : s₁ = s₂ := 
  if h : s.Nontrivial 
  then (e₁.grouped h).deterministic ht hp (e₂.grouped h)
  else e₁.trivial_deterministic h e₂ ht
  
end Execution