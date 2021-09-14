import ReactorModel.Inst.PrecGraph

namespace Inst

variable {ι υ} [ID ι] [Value υ]

def isExecution (rtr₁ rtr₂ : Reactor ι υ) : Prop :=
  ∃ π : PrecGraph rtr₁, π.isAcyclic
  -- ...

end Inst