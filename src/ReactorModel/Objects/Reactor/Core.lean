import ReactorModel.Objects.Reactor.TypeClasses.Basic

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

theorem ext_iff : {rtr₁ rtr₂ : Reactor.Core} → rtr₁ = rtr₂ ↔ 
    rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts ∧ rtr₁.state = rtr₂.state ∧ 
    rtr₁.rcns = rtr₂.rcns ∧ rtr₁.nest  = rtr₂.nest
  | mk .., mk .. => by simp_all [Core.ports, Core.state, Core.rcns, Core.acts, Core.nest]

instance : ReactorType Reactor.Core where
  ports := Reactor.Core.ports
  acts  := Reactor.Core.acts
  state := Reactor.Core.state
  rcns  := Reactor.Core.rcns
  nest  := Reactor.Core.nest

end Core
end Reactor