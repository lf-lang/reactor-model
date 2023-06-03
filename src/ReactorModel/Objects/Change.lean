import ReactorModel.Objects.Component

abbrev Component.Writable.changeType : Component.Writable → Type
  | inp | out | stv  => Value
  | log => Time × Value 

namespace Change

protected structure Normal where
  cpt   : Component.Writable
  id    : ID
  value : cpt.changeType

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
abbrev inp (i : ID) (v : Value) : Change :=
  .norm $ { cpt := .inp, id := i, value := v }

@[match_pattern]
abbrev out (i : ID) (v : Value) : Change :=
  .norm $ { cpt := .out, id := i, value := v }

@[match_pattern]
abbrev stv (i : ID) (v : Value) : Change :=
  .norm $ { cpt := .stv, id := i, value := v }

@[match_pattern]
abbrev act (i : ID) (t : Time) (v : Value) : Change :=
  .norm $ { cpt := .log, id := i, value := (t, v) }

inductive Targets : Change → Component.Valued → ID → Prop
  | intro : Targets (norm ⟨cpt, i, v⟩) cpt i

theorem Targets.norm_not (h : ¬Targets (norm ⟨c, j, v⟩) cpt i) : cpt ≠ c ∨ i ≠ j := by
  by_contra hc
  simp [not_or] at hc
  exact hc.left ▸ hc.right ▸ h $ .intro 

def target : Change → Option (Component.Writable × ID)
  | norm ⟨cpt, i, _⟩ => (cpt, i)
  | «mut» ..         => none

inductive IsNormal : Change → Prop
  | intro : IsNormal (norm _)

inductive IsMutation : Change → Prop
  | intro : IsMutation («mut» _)

inductive IsPort : Change → Prop
  | intro : IsPort (prt ..)

inductive IsAction : Change → Prop 
  | intro : IsAction (act ..)

end Change
