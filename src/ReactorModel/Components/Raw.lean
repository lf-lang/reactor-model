import ReactorModel.Primitives

open Ports

namespace Raw

-- This block basically just serves the purpose of defining `Raw.Reactor`.
-- We later define an extension of `Raw.Reactor` called `Reactor`, which adds
-- all of the necessary constraints on it subcomponents.
-- Those subcomponents are then (re-)defined as well,
-- by using the definition of `Reactor`.
--
-- For more information on the use case of each component, cf. the definitions
-- of their non-`Raw` counterparts.
mutual 

protected inductive Change (ι υ) [i : ID ι] [v : Value υ]
  | port (target : ι) (value : υ)
  | state (target : ι) (value : υ)
  | connect (src : ι) (dst : ι)
  | disconnect (src : ι) (dst : ι)
  | create (rtr : Raw.Reactor ι υ) (id : ι)
  | delete (rtrID : ι)

protected inductive Reaction (ι υ) [i : ID ι] [v : Value υ]
  | mk 
    (deps : Ports.Role → Finset ι) 
    (triggers : Finset ι)
    (children : Finset ι)
    (body : Ports ι υ → StateVars ι υ → List (Raw.Change ι υ))

protected inductive Reactor (ι υ) [i : ID ι] [v : Value υ]
  | mk 
    (ports : Ports ι υ) 
    (roles : ι ▸ Ports.Role)
    (state : StateVars ι υ)
    (rcns : ι → Option (Raw.Reaction ι υ))
    (nest : ι → Option (Raw.Reactor ι υ))
    (prios : PartialOrder ι)

-- This is just a sanity check, to make sure that the above definition of reactors
-- actually allows them to be constructed.
deriving Inhabited

end

end Raw

variable {ι υ} [ID ι] [Value υ]

namespace Raw.Change 

-- Cf. `Change.mutates`.
def mutates : Raw.Change ι υ → Prop
  | port _ _       => False
  | state _ _      => False
  | connect _ _    => True
  | disconnect _ _ => True
  | create _ _     => True
  | delete _       => True
end Raw.Change

namespace Raw.Reaction

-- These definitions give us the projections that would usually be generated for a structure.
def deps :     Raw.Reaction ι υ → (Ports.Role → Finset ι)                             | mk d _ _ _ => d
def triggers : Raw.Reaction ι υ → Finset ι                                            | mk _ t _ _ => t
def children : Raw.Reaction ι υ → Finset ι                                            | mk _ _ c _ => c
def body :     Raw.Reaction ι υ → (Ports ι υ → StateVars ι υ → List (Raw.Change ι υ)) | mk _ _ _ b => b

-- Cf. `Reaction.isNorm`.
def isNorm (rcn : Raw.Reaction ι υ) : Prop :=
  ∀ i s c, c ∈ (rcn.body i s) → ¬c.mutates

-- Cf. `Reaction.isMut`.
def isMut (rcn : Raw.Reaction ι υ) : Prop := ¬rcn.isNorm

end Raw.Reaction

namespace Raw.Reactor

-- These definitions give us the projections that would usually be generated for a structure.
def ports : Raw.Reactor ι υ → Ports ι υ                       | mk p _ _ _ _ _ => p
def roles : Raw.Reactor ι υ → (ι ▸ Ports.Role)                | mk _ r _ _ _ _ => r
def state : Raw.Reactor ι υ → StateVars ι υ                   | mk _ _ s _ _ _ => s 
def rcns :  Raw.Reactor ι υ → (ι → Option (Raw.Reaction ι υ)) | mk _ _ _ r _ _ => r
def nest :  Raw.Reactor ι υ → (ι → Option (Raw.Reactor ι υ))  | mk _ _ _ _ n _ => n
def prios : Raw.Reactor ι υ → PartialOrder ι                  | mk _ _ _ _ _ p => p 

-- An accessor for ports, that allows us to separate them by port role.
noncomputable def ports' (rtr : Raw.Reactor ι υ) (r : Ports.Role) : Ports ι υ := 
  rtr.ports.filter (λ i => rtr.roles i = r)

end Raw.Reactor