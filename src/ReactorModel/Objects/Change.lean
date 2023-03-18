import ReactorModel.Objects.Component

open Reactor

abbrev Reactor.Component.Valued.changeType : Component.Valued → Type
  | prt _ | stv  => Value
  | act => Time × Value 

namespace Change

protected structure Normal where
  cmp   : Component.Valued
  id    : ID
  value : cmp.changeType

opaque Reactor.Class : Type

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

instance : Coe Change.Normal Change where
  coe := norm

instance : Coe Change.Mutation Change where
  coe := «mut»

@[match_pattern]
abbrev prt (k : Kind) (i : ID) (v : Value) : Change :=
  .norm $ { cmp := .prt k, id := i, value := v }

@[match_pattern]
abbrev stv (i : ID) (v : Value) : Change :=
  .norm $ { cmp := .stv, id := i, value := v }

@[match_pattern]
abbrev act (i : ID) (t : Time) (v : Value) : Change :=
  .norm $ { cmp := .act, id := i, value := (t, v) }

inductive Targets : Change → Component.Valued → ID → Prop
  | intro {cmp v} : Targets (norm ⟨cmp, i, v⟩) cmp i

theorem Targets.norm_not {cmp} (h : ¬Targets (norm ⟨c, j, v⟩) cmp i) : cmp ≠ c ∨ i ≠ j := by
  by_contra hc
  simp [not_or] at hc
  exact absurd .intro (hc.left ▸ hc.right ▸ h)

inductive IsNormal : Change → Prop
  | intro : IsNormal (norm _)

inductive IsMutation : Change → Prop
  | intro : IsMutation («mut» _)

inductive IsPort : Change → Prop
  | intro : IsPort (prt ..)

inductive IsAction : Change → Prop 
  | intro : IsAction (act ..)

end Change