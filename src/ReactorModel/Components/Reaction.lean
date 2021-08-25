import ReactorModel.Primitives

open Reactor
open Reactor.Ports

variable (ι υ) [ID ι] [Value υ]

structure Reaction :=
  (deps : Ports.Role → Finset ι) 
  (triggers : Finset ι)
  (body : Ports ι υ → StateVars ι υ → (Ports ι υ × StateVars ι υ))
  (tsSubInDeps : triggers ⊆ deps Role.in)
  (inDepOnly : ∀ {i i'} s, (i =[deps Role.in] i') → body i s = body i' s)
  (outDepOnly : ∀ i s {o}, (o ∉ deps Role.out) → (body i s).fst[o] = none)

namespace Reaction

instance : CoeFun (Reaction ι υ) (λ _ => Ports ι υ → StateVars ι υ → (Ports ι υ × StateVars ι υ)) where
  coe rcn := rcn.body

def triggersOn (rcn : Reaction ι υ) (p : Ports ι υ) : Prop :=
  ∃ (t : ι) (v : υ), t ∈ rcn.triggers ∧ p[t] = some v

end Reaction
