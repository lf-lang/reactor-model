import ReactorModel.Components.Reactor.Basic
import ReactorModel.Time 

-- In the semi-formal definition of the Reactor model, reactions' bodies are defined
-- as "opaque code" that has access to a set of APIs for settings ports' values, 
-- connecting ports, creating reactors, etc. The definition of a reaction's body used
-- in *this* formalization is as a function of type `Input ID Value → List (Change ID Value)`.
-- That is, we ignore all side effects that a reaction could have and only consider the
-- part that is relevant to the reactor system: the API calls. 
-- These API calls are formalized by the `Change` type:
inductive Change
  | port (target : ID) (value : Value)
  | state (target : ID) (value : Value)
  | action (target : ID) (time : Time) (value : Value)
  | connect (src : ID) (dst : ID)
  | disconnect (src : ID) (dst : ID)
  | create (rtr : Reactor)
  | delete (rtr : ID)

namespace Change

abbrev Equiv : Change → Change → Prop
  | port ..,       port ..       => True 
  | state ..,      state ..      => True 
  | action ..,     action ..     => True 
  | connect ..,    connect ..    => True
  | disconnect .., disconnect .. => True 
  | create ..,     create ..     => True 
  | delete ..,     delete ..     => True 
  | _,             _             => False

notation c₁ " ≈ " c₂ => Equiv c₁ c₂

def target : Change → Option ID 
  | port t ..   => t
  | state t ..  => t
  | action t .. => t
  | _           => none
  
-- Instances of `Change` can be split into two groups: 
-- those which express a mutation to the structure of a reactor system, 
-- and those which don't.
-- This distinction will be used later to differentiate between "normal"
-- reactions and mutations, as normal reactions are not allowed to produce
-- mutating changes.
def mutates : Change → Prop 
  | port ..       => False
  | state ..      => False
  | action ..     => False
  | connect ..    => True
  | disconnect .. => True
  | create ..     => True
  | delete ..     => True

-- It is decidable whether a change mutates.
instance : DecidablePred mutates 
  | port ..       => isFalse (by simp [mutates])
  | state ..      => isFalse (by simp [mutates])
  | action ..     => isFalse (by simp [mutates])
  | connect ..    => isTrue  (by simp [mutates])
  | disconnect .. => isTrue  (by simp [mutates])
  | create ..     => isTrue  (by simp [mutates])
  | delete ..     => isTrue  (by simp [mutates])

theorem target_none_iff_mutates (c : Change) : c.target = none ↔ c.mutates := by
  cases c <;> simp only [target, mutates]

end Change
