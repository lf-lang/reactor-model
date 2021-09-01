import ReactorModel.Components

open Ports 
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
def rcnsAreInternallyDep (rcn₁ rcn₂ : ι) (σ : Reactor ι υ) : Prop := 
  ∃ (i : ι) (rtr : Reactor ι υ), 
    (σ &[Cmp.rcn] rcn₁) = some i ∧
    (σ &[Cmp.rcn] rcn₂) = some i ∧
    (σ *[Cmp.rtr] i)    = some rtr ∧
    rtr.prios.lt rcn₁ rcn₂

notation r₁ " <[" σ "]> " r₂ => PrecGraph.rcnsAreInternallyDep r₁ r₂ σ

def rcnsAreExternallyDep (rcn₁ rcn₂ : ι) (σ : Reactor ι υ) : Prop :=
  ∃ (c : Connection ι) (rn₁ rn₂ : Reaction ι υ),
    c ∈ σ.nest.cns ∧ 
    (σ *[Cmp.rcn] rcn₁) = some rn₁ ∧ 
    (σ *[Cmp.rcn] rcn₂) = some rn₂ ∧
    c.src ∈ rn₁.deps Role.out ∧ 
    c.dst ∈ rn₂.deps Role.in

notation r₁ " >[" σ "]< " r₂ => PrecGraph.rcnsAreExternallyDep r₁ r₂ σ

end PrecGraph

structure PrecGraph (σ : Reactor ι υ) :=
  (rcns : ι ▸ Reaction ι υ)
  (edges : Finset (PrecGraphEdge ι))
  (wfIDs : rcns.ids = σ &[Cmp.rcn])
  (wfData : ∀ i, rcns i = σ *[Cmp.rcn] i)
  (wfEdges : 
    ∀ e, e ∈ edges ↔ 
      (e.src ∈ rcns.ids) ∧ 
      (e.dst ∈ rcns.ids) ∧ 
      ((e.src <[σ]> e.dst) ∨ (e.src >[σ]< e.dst))
  )