import ReactorModel.Primitives

opaque Reactor.Class : Type

-- In the semi-formal definition of the Reactor model, reactions' bodies are defined
-- as "opaque code" that has access to a set of APIs for settings ports' values, 
-- connecting ports, creating reactors, etc. The definition of a reaction's body used
-- in *this* formalization is as a function of type `Input ID Value → List (Change ID Value)`.
-- That is, we ignore all side effects that a reaction could have and only consider the
-- part that is relevant to the reactor system: the API calls. 
-- These API calls are formalized by the `Change` type:
namespace Change

protected inductive Normal
  | port   (kind : Kind) (port : ID) (value : Value)
  | state  (var : ID) (value : Value)
  | action (action : ID) (time : Time) (value : Value)

protected inductive Mutation
  | connect    (srcPort : ID) (dstPort : ID)
  | disconnect (srcPort : ID) (dstPort : ID)
  | create     («class» : Reactor.Class)
  | delete     (rtr : ID)

end Change

inductive Change
  | norm  : Change.Normal → Change
  | «mut» : Change.Mutation → Change 

namespace Change

variable [DecidableEq ID]

instance : Coe Change.Normal Change where
  coe := norm

instance : Coe Change.Mutation Change where
  coe := «mut»

@[match_pattern]
abbrev port : Kind → ID → Value → Change := (.norm $ .port · · ·) 

@[match_pattern]
abbrev state : ID → Value → Change := (.norm $ .state · ·) 

@[match_pattern]
abbrev action : ID → Time → Value → Change := (.norm $ .action · · ·) 

inductive IsNormal : Change → Prop
  | intro : IsNormal (norm _)

inductive IsMutation : Change → Prop
  | intro : IsMutation («mut» _)

namespace Normal 

def id : Change.Normal → ID
  | port _ i _ | state i .. | action i .. => i

def value : Change.Normal → Value
  | port _ _ v | state _ v | action _ _ v => v

end Normal

inductive IsPort : Change → Prop
  | intro : IsPort (port ..)

inductive IsPortᵢ (k : Kind) (i : ID) : Change → Prop
  | intro : IsPortᵢ k i (port k i _)

theorem IsPortᵢ.iff_kind_and_id_eq : IsPortᵢ k i (port l j v) ↔ (j = i) ∧ (l = k) where
  mp | intro .. => ⟨rfl, rfl⟩ 
  mpr h := h.left ▸ h.right ▸ .intro

def portValue? (k : Kind) (i : ID) : Change → Option Value
  | port l j v => if (l = k) ∧ (j = i) then some v else none
  | _ => none

theorem portValue?_some (h : portValue? k i c = some v) : c = port k i v := by
  cases c <;> try cases ‹Change.Normal›  
  all_goals simp [portValue?] at h
  split at h <;> simp_all      

theorem IsPortᵢ.iff_portValue?_some : (IsPortᵢ k i c) ↔ (∃ v, c.portValue? k i = some v) where
  mp  | intro      => by simp [portValue?] 
  mpr | .intro v h => by simp [portValue?_some h, intro]

theorem IsPortᵢ.not_iff_portValue?_none : ¬(IsPortᵢ k i c) ↔ (c.portValue? k i = none) :=
  sorry

inductive IsState : Change → Prop
  | intro : IsState (state _ _)

inductive IsStateᵢ (i : ID) : Change → Prop
  | intro : IsStateᵢ i (state i _)

theorem IsStateᵢ.iff_id_eq : IsStateᵢ i (state j v) ↔ j = i where
  mp | intro .. => rfl
  mpr h := h ▸ .intro

def stateValue? (i : ID) : Change → Option Value
  | state j v => if j = i then some v else none
  | _ => none

theorem stateValue?_some (h : stateValue? i c = some v) : c = state i v := by
  cases c <;> try cases ‹Change.Normal›  
  all_goals simp [stateValue?] at h
  split at h <;> simp_all      

theorem IsStateᵢ.iff_stateValue?_some : (IsStateᵢ i c) ↔ (∃ v, c.stateValue? i = some v) where
  mp  | intro      => by simp [stateValue?] 
  mpr | .intro v h => by simp [stateValue?_some h, intro]

theorem IsStateᵢ.not_iff_stateValue?_none : ¬(IsStateᵢ i c) ↔ (c.stateValue? i = none) :=
  sorry

inductive IsAction : Change → Prop 
  | intro : IsAction (action _ _ _)

inductive IsActionᵢ (i : ID) : Change → Prop
  | intro : IsActionᵢ i (action i _ _)

inductive IsActionₜ (i : ID) (t : Time) : Change → Prop
  | intro : IsActionₜ i t (action i t _)

theorem IsActionᵢ.iff_id_eq : IsActionᵢ i (action j t v) ↔ j = i where
  mp | intro .. => rfl
  mpr h := h ▸ .intro

theorem IsActionₜ.not_to_ne_ids_or_ne_time (h : ¬IsActionₜ i t (action j u v)) : j ≠ i ∨ u ≠ t := by
  by_contra hc
  simp [not_or] at hc
  exact absurd (hc.left ▸ hc.right ▸ .intro) h

def actionValue? (i : ID) (t : Time) : Change → Option Value
  | action j u v  => if j = i ∧ u = t then some v else none
  | _ => none

theorem actionValue?_some (h : actionValue? i t c = some v) : c = action i t v := by
  cases c <;> try cases ‹Change.Normal›  
  all_goals simp [actionValue?] at h
  split at h <;> simp_all

theorem IsActionₜ.iff_actionValue?_some : 
    (IsActionₜ i t c) ↔ (∃ v, c.actionValue? i t = some v) where
  mp  | intro      => by simp [actionValue?] 
  mpr | .intro v h => by simp [actionValue?_some h, intro]

theorem IsActionₜ.not_iff_actionValue?_none : ¬(IsActionₜ i t c) ↔ (c.actionValue? i t = none) :=
  sorry

end Change
