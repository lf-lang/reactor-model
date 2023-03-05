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

variable [DecidableEq ID]

-- TODO: Remove the Bool-based functions.

abbrev isPort : Change → Bool 
  | port .. => true
  | _ => false

inductive IsPort (i : ID) : Change → Prop
  | intro : IsPort i (.port i v)

theorem IsPort.iff_id_eq : IsPort j (.port i v) ↔ i = j where
  mp | intro .. => rfl
  mpr h := h ▸ .intro

abbrev isState : Change → Bool 
  | state .. => true
  | _ => false

inductive IsState (i : ID) : Change → Prop
  | intro : IsState i (.state i v)

theorem IsState.iff_id_eq : IsState j (.state i v) ↔ i = j where
  mp | intro .. => rfl
  mpr h := h ▸ .intro

abbrev isAction : Change → Bool 
  | action .. => true
  | _ => false

inductive IsAction (i : ID) : Change → Prop
  | intro : IsAction i (.action i t v)

theorem IsAction.iff_id_eq : IsAction j (.action i t v) ↔ i = j where
  mp | intro .. => rfl
  mpr h := h ▸ .intro

inductive IsActionAt (i : ID) (t : Time) : Change → Prop
  | intro : IsActionAt i t (.action i t v)

theorem not_IsActionAt_ne_ids_or_ne_time 
    (h : ¬IsActionAt j t (.action i t' v)) : i ≠ j ∨ t' ≠ t := by
  by_contra hc
  simp [not_or] at hc
  exact absurd (hc.left ▸ hc.right ▸ .intro) h

def isActionForTime (t : Time) : Change → Bool 
  | action _ t' _ => t = t'
  | _ => false

def portValue? (t : ID) : Change → Option Value
  | port t' v => if t' = t then some v else none
  | _ => none

def stateValue? (i : ID) : Change → Option Value
  | state j v => if j = i then some v else none
  | _ => none

def actionValue? (i : ID) (t : Time) : Change → Option Value
  | action j t' v  => if i = j ∧ t = t' then some v else none
  | _ => none

theorem portValue?_some {c : Change} : 
  (c.portValue? t = some v) → (c = .port t v) := by
  intro h
  cases c 
  case port t v =>
    simp [portValue?] at h
    split at h <;> simp_all      
  all_goals simp [portValue?] at *

theorem IsPort.iff_portValue?_some : IsPort i c ↔ ∃ v, c.portValue? i = some v where
  mp  | intro      => by simp [portValue?] 
  mpr | .intro v h => by simp [portValue?_some h, intro]

theorem not_IsPort_iff_portValue?_none : ¬(IsPort i c) ↔ c.portValue? i = none :=
  sorry

theorem stateValue?_some {c : Change} : 
  (c.stateValue? t = some v) → (c = .state t v) := by
  intro h
  cases c 
  case state t v =>
    simp [stateValue?] at h
    split at h <;> simp_all      
  all_goals simp [stateValue?] at *

theorem IsState.iff_stateValue?_some : IsState i c ↔ ∃ v, c.stateValue? i = some v where
  mp  | intro      => by simp [stateValue?] 
  mpr | .intro v h => by simp [stateValue?_some h, intro]

theorem not_IsState_iff_stateValue?_none : ¬(IsState i c) ↔ c.stateValue? i = none :=
  sorry

theorem actionValue?_some {c : Change}: 
  (c.actionValue? i t = some v) → (c = .action i t v) := by
  sorry

theorem IsActionAt.iff_actionValue?_some : IsActionAt i t c ↔ ∃ v, c.actionValue? i t = some v where
  mp  | intro      => by simp [actionValue?] 
  mpr | .intro v h => by sorry

theorem not_IsActionAt_iff_actionValue?_none : ¬(IsActionAt i t c) ↔ c.actionValue? i t = none :=
  sorry

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
