import ReactorModel.Primitives
import ReactorModel.LGraph

open Reactor
open Reactor.Ports

structure Connection (ι) where
  src : ι
  dst : ι

instance (ι) : LGraph.Edge (Connection ι) ι := 
  ⟨Connection.src, Connection.dst⟩

namespace Component

-- This block basically just serves the purpose of defining `Component.Reactor`.
-- We later define a version of `Component.Reactor` called `Reactor`, which adds
-- all of the necessary constraints on it subcomponents.
-- Those subcomponents are then (re-)defined as well, by using the definition of 
-- `Reactor`.
mutual 

inductive MutationOutput (ι υ)
  | mk
    (prtVals : Ports ι υ)
    (state   : StateVars ι υ)
    (newCns  : List (ι × ι))
    (delCns  : List (ι × ι))
    (newRtrs : List (Reactor ι υ))
    (delRtrs : Finset ι)

inductive Mutation (ι υ)
  | mk 
    (deps : Ports.Role → Finset ι) 
    (triggers : Finset ι)
    (body : Ports ι υ → StateVars ι υ → MutationOutput ι υ)

inductive Reactor (ι υ)
  | mk 
    (ports : Ports.Role → Ports ι υ) 
    (state : StateVars ι υ)
    (rcns : ι ⇀ Mutation ι υ)
    (muts : ι ⇀ Mutation ι υ)
    (prios : PartialOrder ι)
    (nest : Network ι υ)
  
inductive Network (ι υ)
  | mk 
    (nodes : ι ⇀ (Reactor ι υ))
    (edges : Finset (Connection ι))

end

-- This is just a sanity check, to make sure that this definition of reactors actually allows them to be constructed.
instance : Inhabited (Reactor ι υ) where
  default := Reactor.mk Inhabited.default Inhabited.default Inhabited.default Inhabited.default sorry (Network.mk Inhabited.default Inhabited.default)

namespace MutationOutput

def prtVals : MutationOutput ι υ → Ports ι υ          | mk p _ _ _ _ _ => p
def state :   MutationOutput ι υ → StateVars ι υ      | mk _ s _ _ _ _ => s
def newCns :  MutationOutput ι υ → List (ι × ι)       | mk _ _ c _ _ _ => c
def delCns :  MutationOutput ι υ → List (ι × ι)       | mk _ _ _ c _ _ => c
def newRtrs : MutationOutput ι υ → List (Reactor ι υ) | mk _ _ _ _ r _ => r
def delRtrs : MutationOutput ι υ → Finset ι           | mk _ _ _ _ _ r => r

end MutationOutput

namespace Mutation

def deps :     Mutation ι υ → (Ports.Role → Finset ι)                          | mk d _ _ => d
def triggers : Mutation ι υ → (Finset ι)                                       | mk _ t _ => t
def body :     Mutation ι υ → (Ports ι υ → StateVars ι υ → MutationOutput ι υ) | mk _ _ b => b

end Mutation

namespace Reactor

def ports : Reactor ι υ → (Ports.Role → Ports ι υ) | mk p _ _ _ _ _ => p
def state : Reactor ι υ → StateVars ι υ            | mk _ s _ _ _ _ => s 
def rcns :  Reactor ι υ → (ι ⇀ Mutation ι υ)       | mk _ _ r _ _ _ => r
def muts :  Reactor ι υ → (ι ⇀ Mutation ι υ)       | mk _ _ _ m _ _ => m
def prios : Reactor ι υ → PartialOrder ι           | mk _ _ _ _ p _ => p 
def nest :  Reactor ι υ → Network ι υ              | mk _ _ _ _ _ n => n

end Reactor

namespace Network

def nodes : Network ι υ → (ι ⇀ Reactor ι υ)     | mk n _ => n
def edges : Network ι υ → Finset (Connection ι) | mk _ e => e

end Network

protected def Reactor.lt : Reactor ι υ -> Reactor ι υ -> Prop := sorry
protected def Reactor.ltWF (x: Reactor ι υ): Acc Reactor.lt x := sorry

def Reactor.mutIsMem (rtr : Reactor ι υ) (m : Mutation ι υ) : Prop :=
  WellFounded.fixF (λ r mutIsMem => 
    (∃ i, r.muts i = some m) ∨ (∃ i r', r.nest.nodes i = some r' ∧ mutIsMem r' sorry)
  ) rtr (Reactor.ltWF rtr)

end Component