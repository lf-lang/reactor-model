import ReactorModel.Components

open Ports 
open Classical

namespace PrecGraph

variable (ι) {υ} [ID ι] [Value υ]

-- A type for edges between reactions (identified by their IDs) in a precedence graph.
-- An edge from `src` to `dst` will mean that the reaction identified by `src` takes precedence over `dst`.
protected structure Edge where
  src : ι
  dst : ι

variable {ι}

-- The condition under which two reactions are "internally dependent" in a given reactor.
-- This is the case if both reactions live in the same reactor and the first reaction
-- has a higher priority than the second (`rtr.prios.lt i₁ i₂` means that `i₁` has a
-- higher priority than `i₂`).  
--
-- It's important here to compare *identity* of the parent (`i`) instead of just:
-- `(σ *[Cmp.rtr] i₁) = some rtr ∧ (σ *[Cmp.rtr] i₂) = some rtr`
-- because this condition could also hold when `i₁` and `i₂` have different parents.
def internalDependence (i₁ i₂ : ι) (σ : Reactor ι υ) : Prop := 
  ∃ (p : ι) (rtr : Reactor ι υ),
    (σ & i₁) = p ∧ 
    (σ & i₂) = p ∧
    (σ *[Cmp.rtr] p) = rtr ∧
    rtr.prios.lt i₁ i₂

-- The condition under which two reactions are "externally dependent" in a 
-- given reactor. This is the case if they share a port as anti-/dependency.
def externalDependence (i₁ i₂ : ι) (σ : Reactor ι υ) : Prop :=
  ∃ (rcn₁ rcn₂ : Reaction ι υ),
    (σ *[Cmp.rcn] i₁) = rcn₁ ∧
    (σ *[Cmp.rcn] i₂) = rcn₂ ∧ 
    (rcn₁.deps Role.out) ∩ (rcn₂.deps Role.in) ≠ ∅ 

def mutationDependence (iₘ iᵣ : ι)  (σ : Reactor ι υ) : Prop :=
  sorry -- Marten's PhD: Algorithm 9 Line 7

inductive rcnsAreDependent (i₁ i₂ : ι) (σ : Reactor ι υ) : Prop 
  | internal (_ : internalDependence i₁ i₂ σ)
  | external (_ : externalDependence i₁ i₂ σ)
  | mutation (_ : mutationDependence i₁ i₂ σ)

structure Edge.isRequiredFor (e : PrecGraph.Edge ι) (σ : Reactor ι υ) : Prop where
  srcMem : e.src ∈ (σ *[Cmp.rcn]).ids
  dstMem : e.dst ∈ (σ *[Cmp.rcn]).ids
  dep    : rcnsAreDependent e.src e.dst σ

end PrecGraph

variable {ι υ} [ID ι] [Value υ]

structure PrecGraph (σ : Reactor ι υ) where
  edges : Finset (PrecGraph.Edge ι)
  wf : edges = { e : PrecGraph.Edge ι | e.isRequiredFor σ }

def PrecGraph.rcns {σ : Reactor ι υ} (π : PrecGraph σ) : ι ▸ Reaction ι υ := σ *[Cmp.rcn]