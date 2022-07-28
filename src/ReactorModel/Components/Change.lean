import ReactorModel.Primitives

opaque Reactor.Class : Type

-- In the semi-formal definition of the Reactor model, reactions' bodies are defined
-- as "opaque code" that has access to a set of APIs for settings ports' values, 
-- connecting ports, creating reactors, etc. The definition of a reaction's body used
-- in *this* formalization is as a function of type `Input ID Value → List (Change ID Value)`.
-- That is, we ignore all side effects that a reaction could have and only consider the
-- part that is relevant to the reactor system: the API calls. 
-- These API calls are formalized by the `Change` type:
inductive Change
  | port (port : ID) (value : Value)
  | state (var : ID) (value : Value)
  | action (action : ID) (time : Time) (value : Value)
  | connect (srcPort : ID) (dstPort : ID)
  | disconnect (srcPort : ID) (dstPort : ID)
  | create («class» : Reactor.Class)
  | delete (rtr : ID)

namespace Change

section

variable [DecidableEq ID]

abbrev isPort : Change → Bool 
  | port .. => true
  | _ => false

abbrev isState : Change → Bool 
  | state .. => true
  | _ => false

abbrev isAction : Change → Bool 
  | action .. => true
  | _ => false

def isActionForTime (t : Time) : Change → Bool 
  | action _ t' _ => t = t'
  | _ => false

def portValue? (t : ID) : Change → Option Value
  | port t' v => if t' = t then some v else none
  | _ => none

def stateValue? (t : ID) : Change → Option Value
  | state t' v => if t' = t then some v else none
  | _ => none

def actionValue? (t : ID) (tm : Time) : Change → Option Value
  | action t' tm' v  => if t' = t ∧ tm' = tm then some v else none
  | _ => none

theorem portValue?_some {c : Change} : 
  (c.portValue? t = some v) → (c = .port t v) := by
  intro h
  cases c 
  case port t v =>
    simp [portValue?] at h
    split at h <;> simp_all      
  all_goals simp [portValue?] at *

theorem stateValue?_some {c : Change} : 
  (c.stateValue? t = some v) → (c = .state t v) := by
  intro h
  cases c 
  case state t v =>
    simp [stateValue?] at h
    split at h <;> simp_all      
  all_goals simp [stateValue?] at *

theorem isPort_iff_portValue?_eq_some {c : Change} :
  c.isPort ↔ (∃ t v, c.portValue? t = some v) := by
  constructor
  case mp =>
    cases c <;> simp [isPort, portValue?]
    case port t v => exists t, v; simp
  case mpr =>
    cases c <;> simp [portValue?]

theorem isState_iff_stateValue?_eq_some {c : Change} :
  c.isState ↔ (∃ t v, c.stateValue? t = some v) := by
  constructor
  case mp =>
    cases c <;> simp [isState, stateValue?]
    case state t v => exists t, v; simp
  case mpr =>
    cases c <;> simp [stateValue?]

theorem isActionForTime_iff_actionValue?_eq_some {c : Change} :
  (c = .action i t v) ↔ (c.actionValue? i t = some v) := by
  constructor
  case mp =>
    intro h
    cases c <;> simp_all [actionValue?]
  case mpr =>
    intro h
    cases c <;> simp_all [actionValue?]
    case action =>
      split at h <;> simp_all

theorem actionValue?_none {c : Change} :
  (c.actionValue? i t = none) → (∀ v, c ≠ .action i t v) := by
  intro h
  cases c
  case action => 
    intro v
    simp [actionValue?] at h
    split at h
    case inl => contradiction
    case inr h' => 
      simp at h' ⊢ 
      intro h hh
      have := h' h
      contradiction
  all_goals simp

end 

def target : Change → Option ID
  | port t .. | state t .. | action t .. => t
  | _                                    => none

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
