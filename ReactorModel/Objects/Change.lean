import ReactorModel.Objects.Component

abbrev Component.Valued.changeType : Component.Valued → Type
  | inp | out | stv  => Value
  | act => Time × Value

namespace Change

protected structure Normal (ι) where
  cpt   : Component.Valued
  id    : ι
  value : cpt.changeType

opaque Reactor.Class : Type

protected inductive Mutation (ι) where
  | connect    (srcPort : ι) (dstPort : ι)
  | disconnect (srcPort : ι) (dstPort : ι)
  | create     («class» : Reactor.Class)
  | delete     (rtr : ι)

end Change

inductive Change (ι) where
  | norm  (n : Change.Normal ι)
  | «mut» (m : Change.Mutation ι)

namespace Change

instance : Coe (Change.Normal ι) (Change ι) where
  coe := norm

instance : Coe (Change.Mutation ι) (Change ι) where
  coe := «mut»

@[match_pattern]
abbrev inp (i : ι) (v : Value) : Change ι :=
  .norm <| { cpt := .inp, id := i, value := v }

@[match_pattern]
abbrev out (i : ι) (v : Value) : Change ι :=
  .norm <| { cpt := .out, id := i, value := v }

@[match_pattern]
abbrev stv (i : ι) (v : Value) : Change ι :=
  .norm <| { cpt := .stv, id := i, value := v }

@[match_pattern]
abbrev act (i : ι) (t : Time) (v : Value) : Change ι :=
  .norm <| { cpt := .act, id := i, value := (t, v) }

inductive Targets : Change ι → Component.Valued → ι → Prop
  | intro : Targets (norm ⟨cpt, i, v⟩) cpt i

theorem Targets.norm_not {j : ι} (h : ¬Targets (norm ⟨c, j, v⟩) cpt i) : cpt ≠ c ∨ i ≠ j := by
  by_contra hc
  simp [not_or] at hc
  exact hc.left ▸ hc.right ▸ h <| .intro

def target : Change ι → Option (Component.Valued × ι)
  | norm ⟨cpt, i, _⟩ => (cpt, i)
  | «mut» ..         => none

inductive IsNormal : Change ι → Prop where
  | intro : IsNormal (norm _)

inductive IsMutation : Change ι → Prop where
  | intro : IsMutation («mut» _)

inductive IsPort : Change ι → Prop where
  | intro : IsPort (prt ..)

inductive IsAction : Change ι → Prop where
  | intro : IsAction (act ..)

end Change
