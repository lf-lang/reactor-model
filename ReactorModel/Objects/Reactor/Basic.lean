import ReactorModel.Objects.Reaction

noncomputable section

abbrev Component.type (α : Type) [Identifiable α] : Component → Type
  | .rtr   => α
  | .rcn   => Reaction α✦
  | .val _ => Value

class Reactor (α : Type) extends Identifiable α where
  get? : α → (cpt : Component) → (α✦ ⇀ cpt.type α)

namespace Reactor

notation rtr "{" cpt "}"        => get? rtr cpt
notation rtr "{" cpt "}{" i "}" => get? rtr cpt i

inductive StrictMember [Reactor α] (cpt : Component) (i) : α → Type
  | final  : (rtr{cpt}{i} = some o) → StrictMember cpt i rtr
  | nested : (rtr₁{.rtr}{j} = some rtr₂) → (StrictMember cpt i rtr₂) → StrictMember cpt i rtr₁

namespace StrictMember

abbrev object [Reactor α] {rtr : α} {i} : (StrictMember cpt i rtr) → cpt.type α
  | final (o := o) _ => o
  | nested _ m       => m.object

end StrictMember

inductive Member [Reactor α] : (cpt : Component) → (i : α✦cpt) → α → Type
  | root   : Member .rtr ⊤ rtr
  | strict : (StrictMember cpt i rtr) → Member cpt i rtr

namespace Member

variable [Reactor α] {rtr rtr₁ : α}

instance : Coe (StrictMember cpt i rtr) (Member cpt i rtr) where
  coe := .strict

@[match_pattern]
abbrev final (h : rtr{cpt}{i} = some o) : Member cpt i rtr :=
  StrictMember.final h

@[match_pattern]
abbrev nested (h : rtr{.rtr}{j} = some rtr') (s : StrictMember cpt i rtr') : Member cpt i rtr :=
  StrictMember.nested h s

abbrev object {rtr : α} : (Member cpt i rtr) → cpt.type α
  | root     => rtr
  | strict s => s.object

end Member

-- The relation lifts the notion of a member having an objects to the notion of an identified
-- component having an object. When `α` is `Hierarchical` there exists at most one objects for any
-- given identified component.
inductive Object [Reactor α] (rtr : α) (cpt : Component) (i : α✦cpt) : cpt.type α → Prop
  | intro (m : Member cpt i rtr) : Object rtr cpt i m.object

def RootEqualUpTo [Reactor α] (cpt : Component) (i : α✦) (rtr₁ rtr₂ : α) : Prop :=
  ∀ {c j}, (c ≠ cpt ∨ j ≠ i) → rtr₁{c}{j} = rtr₂{c}{j}

notation rtr₁ " ≃[" cpt "][" i "] " rtr₂ => RootEqualUpTo cpt i rtr₁ rtr₂

end Reactor
