import ReactorModel.Objects.Reaction

open Reactor (Component)

-- TODO: Split `ports` into `ins` and `outs`.
class ReactorType (α : Type) where
  ports : α → Kind → ID ⇀ Value             
  acts  : α → ID ⇀ Action
  state : α → ID ⇀ Value            
  rcns  : α → ID ⇀ Reaction         
  nest  : α → ID ⇀ α      
 
namespace ReactorType

abbrev cptType [ReactorType α] : Component → Type
  | .rtr     => α 
  | .rcn     => Reaction
  | .val cpt => cpt.type

abbrev cpt? [inst : ReactorType α] : (cpt : Component) → α → ID ⇀ inst.cptType cpt
  | .rtr   => nest 
  | .rcn   => rcns
  | .prt k => (ports · k)
  | .act   => acts
  | .stv   => state

inductive Member [ReactorType α] (cpt : Component) (i : ID) : α → Type _ 
  | final : (i ∈ cpt? cpt rtr) → Member cpt i rtr
  | nest : (nest rtr₁ j = some rtr₂) → (m : Member cpt i rtr₂) → Member cpt i rtr₁

class Extensional (α) extends ReactorType α where
  ext_iff : 
    rtr₁ = rtr₂ ↔ 
    (ports rtr₁ = ports rtr₂) ∧ (acts rtr₁ = acts rtr₂) ∧ (state rtr₁ = state rtr₂) ∧ 
    (rcns rtr₁ = rcns rtr₂) ∧ (nest rtr₁ = nest rtr₂)

@[ext]
theorem Extensional.ext [inst : Extensional α] {rtr₁ rtr₂ : α} : 
    (ports rtr₁ = ports rtr₂) ∧ (acts rtr₁ = acts rtr₂) ∧ (state rtr₁ = state rtr₂) ∧ 
    (rcns rtr₁ = rcns rtr₂) ∧ (nest rtr₁ = nest rtr₂) → rtr₁ = rtr₂ 
  := inst.ext_iff.mpr

end ReactorType