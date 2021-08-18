import ReactorModel.Components.Reactor

open Reactor
open Reactor.Ports
open Component (MutationOutput)

variable (ι υ) [ID ι] [Value υ]

structure Mutation where
  deps : Ports.Role → Finset ι 
  triggers : Finset ι
  body : Ports ι υ → StateVars ι υ → MutationOutput ι υ
  tsSubInDeps : triggers ⊆ deps Role.in
  inDepOnly : ∀ {i i'} s, (i =[deps Role.in] i') → body i s = body i' s
  outDepOnly : ∀ i s {o}, (o ∉ deps Role.out) → (body i s).prtVals.at o = none 

variable {ι υ}

def Reactor.muts (rtr : Reactor ι υ) : ι ⇀ Mutation ι υ := sorry

namespace Mutation

instance : CoeFun (Mutation ι υ) (λ _ => Ports ι υ → StateVars ι υ → MutationOutput ι υ) where
  coe m := m.body

def triggersOn (m : Mutation ι υ) (p : Ports ι υ) : Prop :=
  ∃ (t : ι) (_ : t ∈ m.triggers) (v : υ), p.at t = some v

end Mutation