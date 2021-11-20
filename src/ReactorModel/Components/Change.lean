import ReactorModel.Components.Reactor.Basic

variable (ι υ) [ID ι] [Value υ]

inductive Change
  | port (target : ι) (value : υ)
  | state (target : ι) (value : υ)
  | connect (src : ι) (dst : ι)
  | disconnect (src : ι) (dst : ι)
  | create (rtr : Reactor ι υ) (id : ι)
  | delete (rtrID : ι)

variable {ι υ}

namespace Change

def mutates : Change ι υ → Prop 
  | port _ _       => False
  | state _ _      => False
  | connect _ _    => True
  | disconnect _ _ => True
  | create _ _     => True
  | delete _       => True

end Change