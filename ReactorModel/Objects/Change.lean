import ReactorModel.Objects.Component

abbrev Component.Valued.changeType (ν : Type) : Component.Valued → Type
  | inp | out | stv => ν
  | act => Time × ν

namespace Change

protected structure Normal (α) [Identifiable α] [Valued α] where
  cpt   : Component.Valued
  id    : (α✦)
  value : cpt.changeType α◾

opaque Reactor.Class : Type

protected inductive Mutation (ι) where
  | connect    (srcPort dstPort : ι)
  | disconnect (srcPort dstPort : ι)
  | create     («class» : Reactor.Class)
  | delete     (rtr : ι)

inductive _root_.Change (α) [Identifiable α] [Valued α] where
  | norm  (n : Change.Normal α)
  | «mut» (m : Change.Mutation α✦)

variable [Identifiable α] [Valued α]

instance : Coe (Change.Normal α) (Change α) where
  coe := norm

instance : Coe (Change.Mutation α✦) (Change α) where
  coe := «mut»

@[match_pattern]
abbrev inp (i : α✦) (v : α◾) : Change α :=
  .norm <| { cpt := .inp, id := i, value := v }

@[match_pattern]
abbrev out (i : α✦) (v : α◾) : Change α :=
  .norm <| { cpt := .out, id := i, value := v }

@[match_pattern]
abbrev stv (i : α✦) (v : α◾) : Change α :=
  .norm <| { cpt := .stv, id := i, value := v }

@[match_pattern]
abbrev act (i : α✦) (t : Time) (v : α◾) : Change α :=
  .norm <| { cpt := .act, id := i, value := (t, v) }

inductive Targets : Change α → Component.Valued → α✦ → Prop
  | intro : Targets (norm ⟨cpt, i, v⟩) cpt i

theorem Targets.norm_not {j : α✦} (h : ¬Targets (norm ⟨c, j, v⟩) cpt i) : cpt ≠ c ∨ i ≠ j := by
  by_contra hc
  simp [not_or] at hc
  exact hc.left ▸ hc.right ▸ h <| .intro

def target : Change α → Option (Component.Valued × α✦)
  | norm ⟨cpt, i, _⟩ => (cpt, i)
  | «mut» ..         => none

inductive IsNormal : Change α → Prop where
  | intro : IsNormal (norm _)

inductive IsMutation : Change α → Prop where
  | intro : IsMutation («mut» _)

inductive IsPort : Change α → Prop where
  | intro : IsPort (prt ..)

inductive IsAction : Change α → Prop where
  | intro : IsAction (act ..)

end Change
