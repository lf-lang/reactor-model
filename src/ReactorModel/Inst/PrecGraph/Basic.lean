import ReactorModel.Components

open Ports 
open Classical

variable {ι υ} [ID ι] [Value υ]

namespace PrecGraph

-- Note, this implies: `i₁ ∈ (σ *[Cmp.rcn]).ids ∧ i₂ ∈ (σ *[Cmp.rcn]).ids`
inductive directPrecedence (i₁ i₂ : ι) (σ : Reactor ι υ) : Prop 
  -- The condition under which two reactions are "internally dependent" in a given reactor.
  -- This is the case if both reactions live in the same reactor and the first reaction
  -- has a higher priority than the second (`rtr.prios.lt i₁ i₂` means that `i₁` has a
  -- higher priority than `i₂`).  
  --
  -- It's important here to compare *identity* of the parent (`i`) instead of just:
  -- `(σ *[Cmp.rtr] i₁) = some rtr ∧ (σ *[Cmp.rtr] i₂) = some rtr`
  -- because this condition could also hold when `i₁` and `i₂` have different parents.
  | internal (_ :
      ∃ (p : ι) (rtr : Reactor ι υ),
        (σ & i₁ = p) ∧ 
        (σ & i₂ = p) ∧
        (σ *[Cmp.rtr] p = rtr) ∧
        (rtr.prios.lt i₁ i₂)
    )
  -- The condition under which two reactions are "externally dependent" in a 
  -- given reactor. This is the case if they share a port as anti-/dependency.
  | external (_ :
      ∃ (rcn₁ rcn₂ : Reaction ι υ),
        (σ *[Cmp.rcn] i₁ = rcn₁) ∧
        (σ *[Cmp.rcn] i₂ = rcn₂) ∧ 
        (rcn₁.deps Role.out ∩ rcn₂.deps Role.in ≠ ∅)
    )
  -- Marten's PhD: Algorithm 9 Line 7
  | mutation (_ :
      sorry
    )

end PrecGraph

notation i₁:max "<[" σ "]" i₂:max => PrecGraph.directPrecedence i₁ i₂ σ

variable {ι υ} [ID ι] [Value υ]

structure PrecGraph (σ : Reactor ι υ) where
  edges : Finset (ι × ι)
  wf : edges = { e : ι × ι | e.fst <[σ] e.snd }

def PrecGraph.rcns {σ : Reactor ι υ} (π : PrecGraph σ) : ι ▸ Reaction ι υ := σ *[Cmp.rcn]