import ReactorModel.Components

open Reactor.Ports
open Classical

variable (ι) {υ} [ID ι] [Value υ]

structure PrecGraphEdge where
  src : ι
  dst : ι

variable {ι}

namespace PrecGraph

-- It's important here to compare *identity* of the parent (`i`) instead of just:
-- `(η *[Cmp.rtr] rcn₁) = some rtr ∧ (η *[Cmp.rtr] rcn₂) = some rtr`
-- because this condition could also hold when `rcn₁` and `rcn₂` have different parents.
def rcnsAreInternallyDep (rcn₁ rcn₂ : ι) (η : Network ι υ) : Prop := 
  ∃ (i : ι) (rtr : Reactor ι υ), 
    (η ↑[Cmp.rcn] rcn₁) = some i ∧
    (η ↑[Cmp.rcn] rcn₂) = some i ∧
    (η *[Cmp.rtr] i)    = some rtr ∧
    rtr.prios.lt rcn₁ rcn₂

def rcnsAreExternallDep (rcn₁ rcn₂ : ι) (η : Network ι υ) : Prop :=
  ∃ (c : Connection ι) (rn₁ rn₂ : Reaction ι υ),
    c ∈ η.cns ∧ 
    (η *[Cmp.rcn] rcn₁) = some rn₁ ∧ 
    (η *[Cmp.rcn] rcn₂) = some rn₂ ∧
    c.src ∈ rn₁.deps Role.out ∧ 
    c.dst ∈ rn₂.deps Role.in

end PrecGraph

structure PrecGraph (η : Network ι υ) :=
  (rcns : ι ▸ Reaction ι υ)
  (edges : Finset (PrecGraphEdge ι))
  (wfIDs : rcns.ids = η &[Cmp.rcn])
  (wfData : ∀ i, rcns i = η *[Cmp.rcn] i)
  (wfEdges : 
    ∀ e, e ∈ edges ↔ 
      (e.src ∈ rcns.ids) ∧ 
      (e.dst ∈ rcns.ids) ∧ 
      (PrecGraph.rcnsAreInternallyDep e.src e.dst η ∨ PrecGraph.rcnsAreExternallDep e.src e.dst η)
  )