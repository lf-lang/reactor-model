import ReactorModel.Objects.Reactor.Component

namespace Reactor

protected inductive Core 
  | mk 
    (ports : ID ⇀ Port)
    (acts :  ID ⇀ Time.Tag ⇀ Value)
    (state : ID ⇀ Value)
    (rcns :  ID ⇀ Reaction)
    (nest :  ID → Option Reactor.Core)

namespace Core

protected def ports : Reactor.Core → ID ⇀ Port             | mk p _ _ _ _ => p
protected def acts :  Reactor.Core → ID ⇀ Time.Tag ⇀ Value | mk _ a _ _ _ => a
protected def state : Reactor.Core → ID ⇀ Value            | mk _ _ s _ _ => s 
protected def rcns :  Reactor.Core → ID ⇀ Reaction         | mk _ _ _ r _ => r
protected def nest :  Reactor.Core → ID ⇀ Reactor.Core     | mk _ _ _ _ n => n

open Lean in set_option hygiene false in
macro "def_lineage_type " ns:ident : command => 
  let namespaced name := mkIdentFrom ns $ ns.getId ++ name
  let reactorType := if ns.getId = `Reactor then ns else mkIdentFrom ns $ `Reactor ++ ns.getId
  `(
    protected abbrev componentType : Component → Type _
      | .rtr => $reactorType
      | .rcn => Reaction
      | .prt => Port
      | .act => Time.Tag ⇀ Value
      | .stv => Value

    protected abbrev cmp? : (cmp : Component) → $reactorType → ID ⇀ $(namespaced `componentType) cmp
      | .rtr => $(namespaced `nest)
      | .rcn => $(namespaced `rcns)
      | .prt => $(namespaced `ports)
      | .act => $(namespaced `acts)
      | .stv => $(namespaced `state)

    inductive Lineage (cmp : Component) (i : ID) : $reactorType → Type _
      | final : i ∈ (rtr.cmp? cmp).ids → Lineage cmp i rtr
      | nest : (rtr₁.nest j = some rtr₂) → (Lineage cmp i rtr₂) → Lineage cmp i rtr₁
  )

def_lineage_type Core -- defines `componentType`, `cmp?` and `Lineage`

theorem ext_iff : {rtr₁ rtr₂ : Reactor.Core} → rtr₁ = rtr₂ ↔ 
    rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts ∧ rtr₁.state = rtr₂.state ∧ 
    rtr₁.rcns = rtr₂.rcns ∧ rtr₁.nest  = rtr₂.nest
  | mk .., mk .. => by simp_all [Core.ports, Core.state, Core.rcns, Core.acts, Core.nest]

end Core
end Reactor