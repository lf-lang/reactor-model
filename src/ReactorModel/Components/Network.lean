import ReactorModel.Components.Reactor

open Reactor.Ports

variable (ι υ) [ID ι] [Value υ]

/- TODO -/
structure Network extends LGraph ι (Reactor ι υ) (Connection ι) where
  uniquePortIns : ∀ (c c') (_ : c ∈ toLGraph.edges) (_ : c' ∈ toLGraph.edges), c.dst = c'.dst → c = c'
  /-(wfConnPrts : 
    ∀ c : Connection ι, c ∈ toLGraph.edges → 
      ∃ s, (toLGraph.nodes (ID.rtr c.src) = some s) ∧ (c.src.prt ∈ (s.prts Role.out).ids) ∧
      ∃ d, (l.nodes.lookup e.dst.rtr = some d) ∧ (e.dst.prt ∈ (d.prts role.in).ids)
  )-/

variable {ι υ}

def Reactor.nest (rtr : Reactor ι υ) : Network ι υ := sorry