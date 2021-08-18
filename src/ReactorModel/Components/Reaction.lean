import ReactorModel.Components.Mutation

variable (ι υ) [DecidableEq ι] [Value υ]

structure Reaction extends (Mutation ι υ) :=
  noNewCns  : ∀ i s, (body i s).newCns  = []
  noDelCns  : ∀ i s, (body i s).delCns  = []
  noNewRtrs : ∀ i s, (body i s).newRtrs = []
  noDelRtrs : ∀ i s, (body i s).delRtrs = ∅

open Component
open Reactor

variable {ι υ}

def Reactor.rcns (rtr : Reactor ι υ) : ι ⇀ Reaction ι υ := sorry

namespace Reaction

instance : CoeFun (Reaction ι υ) (λ _ => Ports ι υ → StateVars ι υ → MutationOutput ι υ) where
  coe rcn := rcn.body

def triggersOn (rcn : Reaction ι υ) : Ports ι υ → Prop := rcn.toMutation.triggersOn

end Reaction
