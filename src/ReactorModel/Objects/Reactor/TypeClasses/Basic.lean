import ReactorModel.Objects.Reaction

namespace Reactor

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Component
  | rtr -- Nested reactors
  | rcn -- Reactions
  | prt -- Ports
  | act -- Actions
  | stv -- State variables

namespace Component

abbrev idType : Component → Type _
  | rtr => RootedID
  | _   => ID

instance {cmp : Component} : Coe ID cmp.idType where
  coe i :=
    match cmp with
    | .rtr => .nest i
    | .rcn | .prt | .act | .stv => i

end Component
end Reactor

open Reactor (Component)

class ReactorType (α : Type _) where
  ports : α → ID ⇀ Port             
  acts :  α → ID ⇀ Time.Tag ⇀ Value 
  state : α → ID ⇀ Value            
  rcns :  α → ID ⇀ Reaction         
  nest :  α → ID ⇀ α      

namespace ReactorType

abbrev componentType [ReactorType α] : Component → Type _
  | .rtr => α 
  | .rcn => Reaction
  | .prt => Port
  | .act => Time.Tag ⇀ Value
  | .stv => Value

abbrev cmp? [inst : ReactorType α] : (cmp : Component) → α → ID ⇀ inst.componentType cmp
  | .rtr => nest 
  | .rcn => rcns
  | .prt => ports
  | .act => acts
  | .stv => state

inductive Lineage [ReactorType α] (cmp : Component) (i : ID) : α → Type _ 
  | final : i ∈ (cmp? cmp rtr).ids → Lineage cmp i rtr
  | nest : (nest rtr₁ j = some rtr₂) → (Lineage cmp i rtr₂) → Lineage cmp i rtr₁
  
def Lineage.container [ReactorType α] {cmp} {rtr : α} : Lineage cmp i rtr → Identified α
  | nest _ (nest h l)              => container (nest h l)
  | nest (rtr₁ := con) (j := j) .. => { id := j, obj := con }
  | _                              => { id := ⊤, obj := rtr }

end ReactorType