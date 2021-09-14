import ReactorModel.Components

open Ports 
open Classical

variable (ι) {υ} [ID ι] [Value υ]

-- A type for edges between reactions (identified by their IDs) in a precedence graph.
-- An edge from `src` to `dst` will mean that the reaction identified by `src` takes precedence over `dst`.
structure PrecGraphEdge where
  src : ι
  dst : ι

variable {ι}

namespace PrecGraph

-- The condition under which two reactions are "internally dependent" in a given reactor.
-- This is the case if both reactions live in the same reactor and the first reaction has
-- a higher priority than the second (`rtr.prios.lt rcn₁ rcn₂` means that `rcn₁` has a 
-- higher priority than `rcn₂`).  
--
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

-- The condition under which two reactions are "externally dependent" in a given reactor.
-- This is the case if there exists a connection between an antidpendency of the first and
-- a dependency of the second reaction.
def rcnsAreExternallyDep (rcn₁ rcn₂ : ι) (σ : Reactor ι υ) : Prop :=
  ∃ (c : Connection ι) (rn₁ rn₂ : Reaction ι υ),
    c ∈ σ.nest.cns ∧ 
    (σ *[Cmp.rcn] rcn₁) = some rn₁ ∧ 
    (σ *[Cmp.rcn] rcn₂) = some rn₂ ∧
    c.src ∈ rn₁.deps Role.out ∧ 
    c.dst ∈ rn₂.deps Role.in

notation r₁ " >[" σ "]< " r₂ => PrecGraph.rcnsAreExternallyDep r₁ r₂ σ

end PrecGraph

-- A precedence graph over a given reactor is a (labeled) directed graph of its reactions,
-- which are (pairwise) connected iff they are internally or externally dependent.
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