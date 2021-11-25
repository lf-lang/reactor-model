import ReactorModel.Components.Reactor.Basic

variable (ι υ) [Value υ]

-- In the semi-formal definition of the Reactor model, reactions' bodies are defined
-- as "opaque code" that has access to a set of APIs for settings ports' values, 
-- connecting ports, creating reactors, etc. The definition of a reaction's body used
-- in *this* formalization is as a function of type `Ports ι υ → StateVars ι υ → List (Change ι υ)`.
-- That is, we ignore all side effects that a reaction could have and only consider the
-- part that is relevant to the reactor system: the API calls. 
-- These API calls are formalized by the `Change` type:
inductive Change
  | port (target : ι) (value : υ)
  | state (target : ι) (value : υ)
  | connect (src : ι) (dst : ι)
  | disconnect (src : ι) (dst : ι)
  | create (rtr : Reactor ι υ) (id : ι)
  | delete (rtrID : ι)

variable {ι υ}

namespace Change

-- Instances of `Change` can be split into two groups: 
-- those which express a mutation to the structure of a reactor system, 
-- and those which don't.
-- This distinction will be used later to differentiate between "normal"
-- reactions and mutations, as normal reactions are not allowed to produce
-- mutating changes.
def mutates : Change ι υ → Prop 
  | port _ _       => False
  | state _ _      => False
  | connect _ _    => True
  | disconnect _ _ => True
  | create _ _     => True
  | delete _       => True

-- It is decidable whether a change mutates.
instance : DecidablePred (@mutates ι υ _) := λ c =>
  match c with
  | port _ _       => isFalse (by simp [mutates])
  | state _ _      => isFalse (by simp [mutates])
  | connect _ _    => isTrue (by simp [mutates])
  | disconnect _ _ => isTrue (by simp [mutates])
  | create _ _     => isTrue (by simp [mutates])
  | delete _       => isTrue (by simp [mutates])

end Change