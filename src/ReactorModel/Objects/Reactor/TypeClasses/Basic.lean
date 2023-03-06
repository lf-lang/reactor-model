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

scoped macro "lawfulCoe_nest_proof" : tactic => 
  `(tactic| simp [ReactorType.nest, Partial.map_map, Function.comp, Partial.attach_map_val])

protected class LawfulCoe (α β) [a : ReactorType α] [b : ReactorType β] extends Coe α β where
  ports : b.ports ∘ coe = a.ports                    := by rfl
  acts  : b.acts  ∘ coe = a.acts                     := by rfl
  rcns  : b.rcns  ∘ coe = a.rcns                     := by rfl
  state : b.state ∘ coe = a.state                    := by rfl
  nest  : b.nest  ∘ coe = (Partial.map coe) ∘ a.nest := by lawfulCoe_nest_proof

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

protected class Extensional.LawfulCoe (α β) [ReactorType α] [Extensional β] 
    extends ReactorType.LawfulCoe α β where
  coe_ext_iff : rtr₁ = rtr₂ ↔ (coe rtr₁ = coe rtr₂)

instance [ReactorType α] [e : Extensional β] [c : Extensional.LawfulCoe α β] : Extensional α where
  ext_iff := by
    intro rtr₁ rtr₂ 
    simp [c.coe_ext_iff, e.ext_iff, ←c.ports, ←c.acts, ←c.rcns, ←c.state]
    intros
    rw [←Function.comp_apply (f := nest), ←Function.comp_apply (f := nest), c.nest]
    exact {
      mp := Partial.map_inj (by simp [Function.Injective, c.coe_ext_iff])
      mpr := by simp_all
    }

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