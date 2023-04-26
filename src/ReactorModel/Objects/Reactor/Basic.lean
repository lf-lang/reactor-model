import ReactorModel.Objects.Reaction

noncomputable section

abbrev Component.type [CoeSort ε Type] (ρ : Type) : Component ε → Type
  | .val cpt => cpt.type
  | .rcn     => Reaction
  | .rtr     => ρ 
  | .ext e   => e

class ReactorType (α : Type) where
  Ext        : Type
  extCoeSort : CoeSort Ext Type
  get?       : α → (cpt : Component Ext) → (ID ⇀ cpt.type α)   
 
namespace ReactorType

notation rtr "{" cpt "}"        => get? rtr cpt
notation rtr "{" cpt "}{" i "}" => get? rtr cpt i

instance [r : ReactorType α] : CoeSort r.Ext Type := 
  ReactorType.extCoeSort

abbrev Cpt (α) [r : ReactorType α] : Type :=
  Component r.Ext

inductive StrictMember [ReactorType α] (cpt : Cpt α) (i : ID) : α → Type
  | final  : (rtr{cpt}{i} = some o) → StrictMember cpt i rtr
  | nested : (rtr₁{.rtr}{j} = some rtr₂) → (StrictMember cpt i rtr₂) → StrictMember cpt i rtr₁

namespace StrictMember

def object [ReactorType α] {rtr : α} {cpt : Cpt α} : (StrictMember cpt i rtr) → cpt.type α
  | final (o := o) _ => o
  | nested _ m       => m.object

end StrictMember

inductive Member [ReactorType α] : (cpt : Cpt α) → (i : cpt.idType) → α → Type 
  | root   : Member .rtr ⊤ rtr
  | strict : (StrictMember cpt i rtr) → Member cpt i rtr 

namespace Member

variable [ReactorType α] {rtr rtr₁ : α}

instance : Coe (StrictMember cpt i rtr) (Member cpt i rtr) where
  coe := .strict

@[match_pattern]
abbrev final (h : rtr{cpt}{i} = some o) : Member cpt i rtr := 
  StrictMember.final h

@[match_pattern]
abbrev nested (h : rtr{.rtr}{j} = some rtr') (s : StrictMember cpt i rtr') : Member cpt i rtr := 
  StrictMember.nested h s

def object {rtr : α} : (Member cpt i rtr) → cpt.type α
  | root     => rtr
  | strict s => s.object

end Member

-- The relation lifts the notion of a member having an objects to the notion of an identified 
-- component having an object. When `α` is `Indexable` there exists at most one objects for any 
-- given identified component. 
inductive Object [ReactorType α] (rtr : α) (cpt : Cpt α) (i : cpt.idType) : cpt.type α → Prop
  | intro (m : Member cpt i rtr) : Object rtr cpt i m.object

-- TODO: Find a better name for this.
def RootEqualUpTo [ReactorType α] (cpt : Cpt α) (i : ID) (rtr₁ rtr₂ : α) : Prop :=
  ∀ {c j}, (c ≠ cpt ∨ j ≠ i) → rtr₁{c}{j} = rtr₂{c}{j}

notation rtr₁ " ≃[" cpt "][" i "] " rtr₂ => RootEqualUpTo cpt i rtr₁ rtr₂

end ReactorType