import ReactorModel.Components.Reactor.Basic
import ReactorModel.Time 

variable (ι υ) [Value υ]

-- In the semi-formal definition of the Reactor model, reactions' bodies are defined
-- as "opaque code" that has access to a set of APIs for settings ports' values, 
-- connecting ports, creating reactors, etc. The definition of a reaction's body used
-- in *this* formalization is as a function of type `Input ι υ → List (Change ι υ)`.
-- That is, we ignore all side effects that a reaction could have and only consider the
-- part that is relevant to the reactor system: the API calls. 
-- These API calls are formalized by the `Change` type:
inductive Change
  | port (target : ι) (value : υ)
  | state (target : ι) (value : υ)
  | action (target : ι) (time : Time) (value : υ)
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
  | port ..       => False
  | state ..      => False
  | action ..     => False
  | connect ..    => True
  | disconnect .. => True
  | create ..     => True
  | delete ..     => True

-- It is decidable whether a change mutates.
instance : DecidablePred (@mutates ι υ _) 
  | port ..       => isFalse (by simp [mutates])
  | state ..      => isFalse (by simp [mutates])
  | action ..     => isFalse (by simp [mutates])
  | connect ..    => isTrue  (by simp [mutates])
  | disconnect .. => isTrue  (by simp [mutates])
  | create ..     => isTrue  (by simp [mutates])
  | delete ..     => isTrue  (by simp [mutates])

end Change
