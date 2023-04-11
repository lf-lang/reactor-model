import ReactorModel.Objects.Reaction

noncomputable section

abbrev Component.type (rtrType : Type) : Component → Type
  | .rtr     => rtrType 
  | .rcn     => Reaction
  | .val cpt => cpt.type

-- TODO: Generalize this over the `Component` type, so you can easily add things like connections.
--       In that case you whould have a type class for what constitutes a component type, which e.g.
--       would include requiring a mapping like `Reactor.Component.type` above.
--       How does this notion relate to the notion of functors?
--
-- Note: This approach is analogous to how algebras are defined in category theory, where the 
--       `Component` parameter plays the role of the functor over which the algrabra is defined.
--
-- TODO: Ask Andrès about how to proceed with this algebra based approach. E.g. if there are certain
--       kinds of mappings between algebras over different functors (which would correspond to 
--       reactor types over different kinds of components) which could be useful here.
class ReactorType (α : Type) where
  get? : α → (cpt : Component) → (ID ⇀ cpt.type α)   
 
-- TODO: Introduce notation for `get?` - e.g. `rtr<cpt><i>` or `rtr{cpt}{i}`.

namespace ReactorType

inductive StrictMember [ReactorType α] (cpt : Component) (i : ID) : α → Type
  | final  : (get? rtr cpt i = some o) → StrictMember cpt i rtr
  | nested : (get? rtr₁ .rtr j = some rtr₂) → (StrictMember cpt i rtr₂) → StrictMember cpt i rtr₁

namespace StrictMember

abbrev final' [ReactorType α] {rtr : α} (h : i ∈ get? rtr cpt) : StrictMember cpt i rtr := 
  .final (Partial.mem_iff.mp h).choose_spec

def object [ReactorType α] {rtr : α} : (StrictMember cpt i rtr) → cpt.type α
  | final (o := o) _ => o
  | nested _ m       => m.object

@[ext]
structure _root_.ReactorType.Container (α) where
  id  : WithTop ID 
  rtr : α 

def container [ReactorType α] {rtr : α} : (StrictMember cpt i rtr) → Container α
  | nested _ (.nested h l)           => container (.nested h l)
  | nested (rtr₂ := con) (j := j) .. => { id := j, rtr := con }
  | final _                          => { id := ⊤, rtr := rtr }

end StrictMember

inductive Member [ReactorType α] : (cpt : Component) → (i : cpt.idType) → α → Type 
  | root   :  Member .rtr ⊤ rtr
  | strict : (StrictMember cpt i rtr) → Member cpt i rtr 

namespace Member

variable [ReactorType α] {rtr rtr₁ : α}

instance : Coe (StrictMember cpt i rtr) (Member cpt i rtr) where
  coe := .strict

@[match_pattern]
abbrev final (h : get? rtr cpt i = some o) : Member cpt i rtr := 
  StrictMember.final h

@[match_pattern]
abbrev nested (h : get? rtr .rtr j = some rtr') (s : StrictMember cpt i rtr') : Member cpt i rtr := 
  StrictMember.nested h s

abbrev final' (h : i ∈ get? rtr cpt) : Member cpt i rtr := 
  StrictMember.final' h

def object {rtr : α} : (Member cpt i rtr) → cpt.type α
  | root     => rtr
  | strict s => s.object

end Member

-- The relation lifts the notion of a member having an objects to the notion of an identified 
-- component having an object. When `α` is `Indexable` there exists at most one objects for any 
-- given identified component. 
inductive Object [ReactorType α] (rtr : α) (cpt : Component) (i : cpt.idType) : cpt.type α → Prop
  | intro (m : Member cpt i rtr) : Object rtr cpt i m.object

-- TODO: Find a better name for this.
def RootEqualUpTo [ReactorType α] (cpt : Component) (i : ID) (rtr₁ rtr₂ : α) : Prop :=
  ∀ {c j}, (c ≠ cpt ∨ j ≠ i) → get? rtr₁ c j = get? rtr₂ c j

notation rtr₁ " ≃[" cpt "][" i "] " rtr₂ => RootEqualUpTo cpt i rtr₁ rtr₂

end ReactorType