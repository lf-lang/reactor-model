import ReactorModel.Components.Raw

open Reactor
open Reactor.Ports

variable (ι υ) [ID ι] [Value υ]

def Raw.Reactor.wellFormed (rtr : Raw.Reactor ι υ) : Prop :=
  (∀ m,       m ∈ rtr.muts.values → m.triggers ⊆ m.deps Role.in) ∧                                      /-mutsTsSubInDeps : -/
  (∀ m,       m ∈ rtr.muts.values → ∀ i i' s, (i =[m.deps Role.in] i') → m.body i s = m.body i' s) ∧    /-mutsInDepOnly : -/
  (∀ m,       m ∈ rtr.muts.values → ∀ i s o, (o ∉ m.deps Role.out) → (m.body i s).prtVals[o] = none ) ∧ /-mutsOutDepOnly : -/
  (∀ m r,     m ∈ rtr.muts.values → (m.deps r) ⊆ (rtr.ports r).ids) ∧ -- Is this the way it should be?  /-wfMutDeps : -/
  (∀ rcn r, rcn ∈ rtr.rcns.values → (rcn.deps r) ⊆ (rtr.ports r).ids) ∧                                 /-wfRcnDeps : -/
  (∀ r : Raw.Reactor ι υ, r ∈ rtr.nest.nodes.values → r.wellFormed)                                     /-nestedWf : -/

structure Reactor where
  raw : Raw.Reactor ι υ
  wf : raw.wellFormed  

variable {ι υ} [ID ι] [Value υ]

namespace Reactor

def ports (rtr : Reactor ι υ) : Ports.Role → Ports ι υ := rtr.raw.ports
def state (rtr : Reactor ι υ) : StateVars ι υ          := rtr.raw.state
def prios (rtr : Reactor ι υ) : PartialOrder ι         := rtr.raw.prios

end Reactor
