import ReactorModel.Primitives

open Ports

namespace Raw

-- This block basically just serves the purpose of defining `Raw.Reactor`.
-- We later define an extension of `Raw.Reactor` called `Reactor`, which adds
-- all of the necessary constraints on it subcomponents.
-- Those subcomponents are then (re-)defined as well, by using the definition of `Reactor`.
mutual 

inductive Change (ι υ) [i : ID ι] [v : Value υ]
  | port (target : ι) (value : υ)
  | state (target : ι) (value : υ)
  | connect (src : ι) (dst : ι)
  | disconnect (src : ι) (dst : ι)
  | create (rtr : Reactor ι υ) (id : ι)
  | delete (rtrID : ι)

inductive Reaction (ι υ) [i : ID ι] [v : Value υ]
  | mk 
    (deps : Ports.Role → Finset ι) 
    (triggers : Finset ι)
    (children : Finset ι)
    (body : Ports ι υ → StateVars ι υ → List (Change ι υ))

inductive Reactor (ι υ) [i : ID ι] [v : Value υ]
  | mk 
    (ports : Ports ι υ) 
    (roles : ι ▸ Ports.Role)
    (state : StateVars ι υ)
    (rcns : ι → Option (Reaction ι υ))
    (nest : ι → Option (Reactor ι υ))
    (prios : PartialOrder ι)

end

variable {ι υ} [ID ι] [Value υ]

-- This is just a sanity check, to make sure that this definition of reactors actually allows them to be constructed.
open Inhabited in
instance : Inhabited (Reactor ι υ) where
  default := Reactor.mk default default default default default default

namespace Change 

def mutates : Change ι υ → Bool 
  | port _ _       => false
  | state _ _      => false
  | connect _ _    => true
  | disconnect _ _ => true
  | create _ _     => true
  | delete _       => true

end Change

namespace Reaction

def deps :     Reaction ι υ → (Ports.Role → Finset ι)                         | mk d _ _ _ => d
def triggers : Reaction ι υ → Finset ι                                        | mk _ t _ _ => t
def children : Reaction ι υ → Finset ι                                        | mk _ _ c _ => c
def body :     Reaction ι υ → (Ports ι υ → StateVars ι υ → List (Change ι υ)) | mk _ _ _ b => b

def isNorm (rcn : Reaction ι υ) : Prop :=
  ∀ i s c, c ∈ (rcn.body i s) → ¬c.mutates

def isMut (rcn : Reaction ι υ) : Prop := ¬rcn.isNorm

end Reaction

namespace Reactor

def ports : Reactor ι υ → Ports ι υ                   | mk p _ _ _ _ _ => p
def roles : Reactor ι υ → (ι ▸ Ports.Role)            | mk _ r _ _ _ _ => r
def state : Reactor ι υ → StateVars ι υ               | mk _ _ s _ _ _ => s 
def rcns :  Reactor ι υ → (ι → Option (Reaction ι υ)) | mk _ _ _ r _ _ => r
def nest :  Reactor ι υ → (ι → Option (Reactor ι υ))  | mk _ _ _ _ n _ => n
def prios : Reactor ι υ → PartialOrder ι              | mk _ _ _ _ _ p => p 

-- An accessor for ports, that allows you to separate them by port role.
noncomputable def ports' (rtr : Reactor ι υ) (r : Ports.Role) : Ports ι υ := 
  rtr.ports.filter (λ i => rtr.roles i = r)

end Reactor

end Raw