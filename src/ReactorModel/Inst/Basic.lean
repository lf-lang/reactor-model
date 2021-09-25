import ReactorModel.Inst.PrecGraph

namespace Inst

variable {ι υ} [ID ι] [Value υ]

def isExecOfRcn (rtr₁ rtr₂ : Reactor ι υ) (rcn : ι) : Prop := sorry

notation rtr₁ "-[" rcn "]→ " rtr₂:max => isExecOfRcn rtr₁ rtr₂ rcn

def isExecOfQueue (rtr₁ rtr₂ : Reactor ι υ) : List ι → Prop
  | [] => rtr₁ = rtr₂
  | hd::tl => ∃ rtrₘ, (rtr₁ -[hd]→ rtrₘ) ∧ (isExecOfQueue rtrₘ rtr₂ tl)
  
notation r₁:max " -[" q "]→ " r₂:max => isExecOfQueue r₁ r₂ q

def isPartialExec (rtr₁ rtr₂ : Reactor ι υ) (rem : List ι) : Prop :=
  ∃ (π : PrecGraph rtr₁) (hd : List ι), 
    π.isAcyclic ∧ 
    (hd ++ rem).isCompleteTopoOver π ∧  
    rtr₁ -[hd]→ rtr₂

notation r₁:max " →ₑ " r₂:max " % " rem:max => isPartialExec r₁ r₂ rem

def isExec (rtr₁ rtr₂ : Reactor ι υ) : Prop :=
  rtr₁ →ₑ rtr₂ % []

notation r₁:max " →ₑ " r₂:max => isExec r₁ r₂

end Inst