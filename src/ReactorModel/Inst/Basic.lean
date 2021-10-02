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
  -- TODO: 
  -- Process all of the mutation-aspects of `o`.
  -- Do they need to occur before some of the other aspects?
  -- Should the user actually be able to determine the order of these events,
  -- given by the order in which they call the corresponding API method?

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

inductive exec (σ₁ σ₂ : Reactor ι υ) (remIn remOut : List ι) : Prop
  -- An execution is *short* if it does not cross the boundary of a logical
  -- time step. That is, it only processes reactions from the input remainer (`remIn`)
  -- and does not require the generation of a new reaction queue.
  | short (_ :
      -- TODO: 
      -- This definition enables a trivial partial execution: `l % σ₁ →ₑ σ₁ l`.
      -- Is this ok? If not, will `¬l.empty` solve it?
      ∃ (l : List ι),
        remIn = l ++ remOut ∧
        σ₁ -[l]→ σ₂
    )
  -- An execution is *long* if it crosses the boundary of a logical time step.
  -- That is, it processes all of the reactions from the input remainer (`remIn`),
  -- as well as reactions from the following new reaction queue.
  | long (_ :
      -- TODO:
      -- A consequence of requirement (1) is that the reactions enqueued in a
      -- remainder list can never be from different instantaneous exections.
      -- Hence, any (permitted) reordering within a remainder list will simply
      -- be equivalent to producing a different topological ordering of the
      -- precedence graph generated for that instantaneous step.
      -- So this probably enforces barrier synchronization again.
      -- On the other hand, if we want to allow the generation of a new precedence graph
      -- and derived reaction queue *before* all prior reactions have been executed,
      -- we probably need to figure out what constraints are required for this to be
      -- allowed. 
      -- Perhaps we only need to ensure that all previous mutations have run?
      -- Note, that figuring out when a new precedence graph can be created is not
      -- the same as figuring out in what way the time barrier can be crossed (i.e.
      -- in what way the remainder-queue can be reordered).
      -- If it is in fact the case that all previous mutations have to have run, 
      -- before we can create a new precedence graph, then this puts a bound on the
      -- time range of the reactions that can accumulate in the remainder queue.
      -- Specifically, (assuming requirement (1) will is resolved) they can only come
      -- from two consecutive instantaneous executions (unless we are able to reorder
      -- the remainder queue such that reactions can precede their mutations).
      -- The pattern being: [remaining rcns from step n, mutations from step n + 1, reactions from step n + 1].
      -- Perhaps this means that mutations enforce barrier sync - 
      -- unless we consider which mutations are actually triggered.
      -- E.g. assuming the following remainder queue:
      -- [a1, a2, a3, m1, m2, b1, b2, b3]
      -- Assuming that m1 and m2 are not triggered by the current port assigment,
      -- and additionally assuming that a1, a2 and a3 don't have a connection to m1 and m2,
      -- then we can deduce that m1 and m2 won't be triggered, therefore removing them from
      -- the queue. Aside from opening the possiblity for more reordering in the remainder queue,
      -- this also implies that we can generate a new prec graph.
      --
      -- Is it a problem, that all of the reactions are accumulating in *one* remainder queue?
      -- What happens when we ignore mutations?
      ∃ (σₘ : Reactor ι υ) (π : PrecGraph σₘ) (l : List ι),
        σ₁ -[remIn]→ σₘ ∧ -- (1) 
        π.isAcyclic ∧ 
        (l ++ remOut).isCompleteTopoOver π ∧  
        σₘ -[l]→ σ₂
    ) 

notation i:max " % " σ₁:max "→ₑ" σ₂:max " % " o:max => exec σ₁ σ₂ i o

end Inst