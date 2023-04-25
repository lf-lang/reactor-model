import ReactorModel.Determinism.Trivial 
import ReactorModel.Determinism.Nontrivial

open Classical

namespace Execution

variable [ReactorType.Practical α] {s s₁ s₂ : State α}

-- TODO: This theorem can be proven over non-`Finite` but `LawfulUpdatable`, `Proper` reactors. 
theorem deterministic : 
    (s ⇓* s₁) → (s ⇓* s₂) → (s₁.tag = s₂.tag) → (s₁.progress = s₂.progress) → s₁ = s₂ := 
  if h : s.Nontrivial 
  then nontrivial_deterministic h
  else fun e₁ e₂ ht _ => e₁.trivial_deterministic h e₂ ht
  
end Execution