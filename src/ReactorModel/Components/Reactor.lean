import ReactorModel.Components.Basic

open Reactor

structure Reactor (ι υ) [ID ι] [Value υ] where
  core : Component.Reactor ι υ

  -- *Long list of all of the constraints that need to be enforced on all the subcomponents*

  -- mut_tsSubInDeps : ∀ triggers ⊆ deps Role.in
  -- mut_inDepOnly : ∀ {i i'} s, (i =[deps Role.in] i') → body i s = body i' s
  -- mut_outDepOnly : ∀ i s {o}, (o ∉ deps Role.out) → (body i s).prtVals.at o = none 
  wfRcnDeps : ∀ {rcn : Component.Mutation ι υ} (h : rcn ∈ core.rcns.values) (r : Ports.Role), (rcn.deps r) ⊆ (core.ports r).ids
  wfMutDeps : ∀ {m : Component.Mutation ι υ} (h : m ∈ core.muts.values) (r : Ports.Role), (m.deps r) ⊆ (core.ports r).ids

variable {ι υ} [ID ι] [Value υ]

namespace Reactor

def ports (rtr : Reactor ι υ) : Ports.Role → Ports ι υ := rtr.core.ports
def state (rtr : Reactor ι υ) : StateVars ι υ          := rtr.core.state
def prios (rtr : Reactor ι υ) : PartialOrder ι         := rtr.core.prios

end Reactor
