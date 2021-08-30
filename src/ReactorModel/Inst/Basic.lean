import ReactorModel.Components

namespace Inst

variable {ι υ} [ID ι] [Value υ]

def isExecution (r₁ r₂ : Reactor ι υ) : Prop := sorry
  -- (1) r₁ has an acyclic precedence graph, otherwise execution stops -> false
  -- (2) ...

end Inst