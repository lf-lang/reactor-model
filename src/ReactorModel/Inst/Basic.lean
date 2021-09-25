import ReactorModel.Inst.PrecGraph

open Reactor
open Ports

namespace Inst

variable {ι υ} [ID ι] [Value υ]

def appOfPorts (σ₁ σ₂ : Reactor ι υ) (iₚ : ι) (p : Ports ι υ) : Prop := 
  sorry -- Find a way to apply the ports in a "random" order.

notation σ₁:max " -[" p ", " iₚ "]→ₚ " σ₂:max => appOfPorts σ₁ σ₂ iₚ p

def appOfState (σ₁ σ₂ : Reactor ι υ) (iₚ : ι) (s : StateVars ι υ) : Prop := 
  sorry -- Find a way to apply the state vars in a "random" order.

notation σ₁:max " -[" s ", " iₚ "]→ₛ " σ₂:max => appOfState σ₁ σ₂ iₚ s

def appOfOut (σ₁ σ₂ : Reactor ι υ) (iₚ : ι) (o : RcnOutput ι υ) : Prop :=
  ∃ (σₘ : Reactor ι υ),
    (σ₁ -[o.state,   iₚ]→ₛ σₘ) ∧ 
    (σₘ -[o.prtVals, iₚ]→ₚ σ₂)
  -- TODO: Process all of the mutation-aspects of `o`.

notation σ₁:max " -[" o ", " iₚ "]→ " σ₂:max => appOfOut σ₁ σ₂ iₚ o

def execOfRcn (σ₁ σ₂ : Reactor ι υ) (i : ι) : Prop :=
  ∃ (iₚ : ι) (rtr : Reactor ι υ) (rcn : Reaction ι υ),
    (σ₁ & i = iₚ) ∧
    (σ₁ *[Cmp.rtr] iₚ = rtr) ∧
    (rtr.rcns i = rcn) ∧
    let out := rcn (rtr.ports Role.in) rtr.state
    σ₁ -[out, iₚ]→ σ₂

notation σ₁ " -[" rcn "]→ " σ₂:max => execOfRcn σ₁ σ₂ rcn

def execOfQueue (σ₁ σ₂ : Reactor ι υ) : List ι → Prop
  | [] => σ₁ = σ₂
  | hd::tl => ∃ σₘ, (σ₁ -[hd]→ σₘ) ∧ (execOfQueue σₘ σ₂ tl)
  
notation σ₁:max " -[" q "]→ " σ₂:max => execOfQueue σ₁ σ₂ q

def partialExec (σ₁ σ₂ : Reactor ι υ) (rem : List ι) : Prop :=
  ∃ (π : PrecGraph σ₁) (hd : List ι), 
    π.isAcyclic ∧ 
    (hd ++ rem).isCompleteTopoOver π ∧  
    σ₁ -[hd]→ σ₂

notation σ₁:max " →ₑ " σ₂:max " % " rem:max => partialExec σ₁ σ₂ rem

def exec (σ₁ σ₂ : Reactor ι υ) : Prop :=
  σ₁ →ₑ σ₂ % []

notation σ₁:max " →ₑ " σ₂:max => exec σ₁ σ₂

end Inst