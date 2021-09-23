import ReactorModel.Primitives

open Ports

namespace Raw

-- This block basically just serves the purpose of defining `Raw.Reactor`.
-- We later define an extension of `Raw.Reactor` called `Reactor`, which adds
-- all of the necessary constraints on it subcomponents.
-- Those subcomponents are then (re-)defined as well, by using the definition of `Reactor`.
mutual 

inductive RcnOutput (ι υ) [i : ID ι] [v : Value υ]
  | mk
    (prtVals : Ports ι υ)
    (state   : StateVars ι υ)
    (newCns  : List (ι × ι))
    (delCns  : List (ι × ι))
    (newRtrs : List (Reactor ι υ))
    (delRtrs : List ι)

inductive Reaction (ι υ) [i : ID ι] [v : Value υ]
  | mk 
    (isMut : Bool)
    (deps : Ports.Role → Finset ι) 
    (triggers : Finset ι)
    (body : Ports ι υ → StateVars ι υ → RcnOutput ι υ)

inductive Reactor (ι υ) [i : ID ι] [v : Value υ]
  | mk 
    (ports : Ports.Role → Ports ι υ) 
    (state : StateVars ι υ)
    (rcns : ι → Option (Reaction ι υ))
    (nest : ι → Option (Reactor ι υ))
    (prios : PartialOrder ι)

end

variable {ι υ} [ID ι] [Value υ]

-- This is just a sanity check, to make sure that this definition of reactors actually allows them to be constructed.
open Inhabited in
instance : Inhabited (Reactor ι υ) where
  default := Reactor.mk default default default default default

-- The definitions below are all just structure-like accessors for the fields of the types defined above.

namespace RcnOutput

def prtVals : RcnOutput ι υ → Ports ι υ          | mk p _ _ _ _ _ => p
def state :   RcnOutput ι υ → StateVars ι υ      | mk _ s _ _ _ _ => s
def newCns :  RcnOutput ι υ → List (ι × ι)       | mk _ _ c _ _ _ => c
def delCns :  RcnOutput ι υ → List (ι × ι)       | mk _ _ _ c _ _ => c
def newRtrs : RcnOutput ι υ → List (Reactor ι υ) | mk _ _ _ _ r _ => r
def delRtrs : RcnOutput ι υ → List ι             | mk _ _ _ _ _ r => r

end RcnOutput

namespace Reaction

def isMut :    Reaction ι υ → Bool                                        | mk i _ _ _ => i
def deps :     Reaction ι υ → (Ports.Role → Finset ι)                     | mk _ d _ _ => d
def triggers : Reaction ι υ → (Finset ι)                                  | mk _ _ t _ => t
def body :     Reaction ι υ → (Ports ι υ → StateVars ι υ → RcnOutput ι υ) | mk _ _ _ b => b

end Reaction

namespace Reactor

def ports : Reactor ι υ → (Ports.Role → Ports ι υ)    | mk p _ _ _ _ => p
def state : Reactor ι υ → StateVars ι υ               | mk _ s _ _ _ => s 
def rcns :  Reactor ι υ → (ι → Option (Reaction ι υ)) | mk _ _ r _ _ => r
def nest :  Reactor ι υ → (ι → Option (Reactor ι υ))  | mk _ _ _ n _ => n
def prios : Reactor ι υ → PartialOrder ι              | mk _ _ _ _ p => p 

end Reactor

end Raw