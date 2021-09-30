import ReactorModel.Inst.PrecGraph

open Reactor
open Ports

namespace Inst

variable {ι υ} [ID ι] [Value υ]

-- TODO: Prove that `appOfPorts` and `appOfState` behave the same (respectively),
-- independently of the specific `ID.order`.

def appOfValues (arePorts : Bool) (σ₁ σ₂ : Reactor ι υ) (f : ι ▸ υ) : Prop := 
  ∃ (es : List (ι × υ)), 
    es.toFinset = f.entries ∧ 
    es.sorted (λ l r => l.fst < r.fst) ∧ 
    σ₂ = aux σ₁ arePorts es
where 
  aux (σ : Reactor ι υ) (arePorts : Bool) : List (ι × υ) → Option (Reactor ι υ)
    | [] => σ
    | hd::tl => 
      let σ' := 
        if arePorts 
        then (σ ←[Cmp.prt, hd.fst] hd.snd) 
        else (σ ←[Cmp.stv, hd.fst] hd.snd)
      match σ' with
      | some σ' => aux σ' arePorts tl
      | none => none

def appOfPorts : Reactor ι υ → Reactor ι υ → StateVars ι υ → Prop := appOfValues (arePorts := true)
def appOfState : Reactor ι υ → Reactor ι υ → StateVars ι υ → Prop := appOfValues (arePorts := false)

notation σ₁:max " -[" p "]→ₚ " σ₂:max => appOfPorts σ₁ σ₂ p
notation σ₁:max " -[" s "]→ₛ " σ₂:max => appOfState σ₁ σ₂ s

def appOfOut (σ₁ σ₂ : Reactor ι υ) (o : RcnOutput ι υ) : Prop :=
  ∃ (σₘ : Reactor ι υ),
    σ₁ -[o.state]→ₛ σₘ ∧ 
    σₘ -[o.prtVals]→ₚ σ₂
  -- TODO: Process all of the mutation-aspects of `o`.

notation σ₁:max " -[" o  "]→ₒ " σ₂:max => appOfOut σ₁ σ₂ o

def execOfRcn (σ₁ σ₂ : Reactor ι υ) (i : ι) : Prop :=
  ∃ (iₚ : ι) (rtr : Reactor ι υ) (rcn : Reaction ι υ),
    σ₁ & i = iₚ ∧
    σ₁ *[Cmp.rtr] iₚ = rtr ∧
    rtr.rcns i = rcn ∧
    let out := rcn (rtr.ports' Role.in) rtr.state
    σ₁ -[out]→ₒ σ₂

notation σ₁ " -[" rcn "]→ᵣ " σ₂:max => execOfRcn σ₁ σ₂ rcn

def execOfQueue (σ₁ σ₂ : Reactor ι υ) : List ι → Prop
  | [] => σ₁ = σ₂
  | hd::tl => ∃ σₘ, (σ₁ -[hd]→ᵣ σₘ) ∧ (execOfQueue σₘ σ₂ tl)
  
notation σ₁:max " -[" q "]→ " σ₂:max => execOfQueue σ₁ σ₂ q

inductive partialExec (σ₁ σ₂ : Reactor ι υ) (remIn remOut : List ι) : Prop
  -- A partial execution is *short* if it does not cross the boundary of a logical
  -- time step. That is, it only processes reactions from the input remainer (`remIn`)
  -- and does not require the generation of a new reaction queue.
  | short (_ :
      ∃ (l : List ι), 
        remIn = l ++ remOut ∧
        σ₁ -[l]→ σ₂
    )
  -- A partial execution is *long* if it crosses the boundary of a logical time step.
  -- That is, it processes all of the reactions from the input remainer (`remIn`),
  -- as well as reactions from the following new reaction queue.
  | long (_ :
      ∃ (σₘ : Reactor ι υ) (π : PrecGraph σₘ) (l : List ι),
        σ₁ -[remIn]→ σₘ ∧
        π.isAcyclic ∧ 
        (l ++ remOut).isCompleteTopoOver π ∧  
        σₘ -[l]→ σ₂
    ) 

notation i:max " % " σ₁:max "→ₑ" σ₂:max " % " o:max => partialExec σ₁ σ₂ i o

-- A "traditional" (non-partial) instantaneous execution.
--! This is probably not required.
def exec (σ₁ σ₂ : Reactor ι υ) : Prop :=
  [] % σ₁ →ₑ σ₂ % []

notation σ₁:max " →ₑ " σ₂:max => exec σ₁ σ₂

end Inst