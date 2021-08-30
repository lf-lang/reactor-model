import ReactorModel.Components

open Reactor.Ports
open Classical

variable (ι) {υ} [ID ι] [Value υ]

structure PrecGraphEdge where
  src : ι
  dst : ι

variable {ι}

namespace PrecGraph

def rcnsAreInternallyDep (rcn₁ rcn₂ : ι) (η : Network ι υ) : Prop := sorry --! requires a function that returns the parent for a given id of specific component-type
  -- (i.rtr = i'.rtr) ∧ (i.rcn > i'.rcn)

def rcnsAreExternallDep (rcn₁ rcn₂ : ι) (η : Network ι υ) : Prop := sorry
  -- ∃ e : inst.network.edge, (e ∈ γ.edges) ∧ (e.src ∈ γ.deps i role.out) ∧ (e.dst ∈ γ.deps i' role.in)

end PrecGraph

structure PrecGraph (η : Network ι υ) :=
  (rcns : ι ▸ Reaction ι υ)
  (edges : Finset (PrecGraphEdge ι))
  -- (wfIDs : rcns.ids = η.rcnIDs)
  -- (wfData : ∀ i, rcns i = η.rcn i)
  (wfEdges : 
    ∀ e, e ∈ edges ↔ 
      (e.src ∈ rcns.ids) ∧ 
      (e.dst ∈ rcns.ids) ∧ 
      (PrecGraph.rcnsAreInternallyDep e.src e.dst η ∨ PrecGraph.rcnsAreExternallDep e.src e.dst η)
  )