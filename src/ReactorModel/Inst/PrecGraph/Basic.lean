import ReactorModel.Components

open Ports Classical

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
  | internal (p : ι) 
             (rtr : Reactor ι υ)
             (hi₁ : σ & i₁ = p)
             (hi₂ : σ & i₂ = p)
             (hr  : σ *[Cmp.rtr] p = rtr)
             (hl  : rtr.prios.lt i₁ i₂)
  -- The condition under which two reactions are "externally dependent" in a 
  -- given reactor. This is the case if they share a port as anti-/dependency.
  | external (rcn₁ rcn₂ : Reaction ι υ) 
             (hi₁ : σ *[Cmp.rcn] i₁ = rcn₁)
             (hi₂ : σ *[Cmp.rcn] i₂ = rcn₂)
             (hd  : rcn₁.deps Role.out ∩ rcn₂.deps Role.in ≠ ∅)
  -- Reactions of a nested reactor should only be able to run once all mutations
  -- of the parent reactor have run. Hence we establish a precedence relationship 
  -- between the parent's last (in terms of priority) mutation (if there is one)
  -- and all of the nested reactor's "first" reactions (there can be multiple, as
  -- a partial order can have multiple minimal elements). 
  -- Cf. Marten's PhD thesis: Algorithm 9 Line 7
  | parentMut (p n : ι) 
              (rtrₚ rtrₙ : Reactor ι υ) 
              (hi₁ : σ & i₁ = p)
              (hi₂ : σ & i₂ = n) 
              (hr₁ : σ *[Cmp.rtr] p = rtrₚ)
              (hr₂ : σ *[Cmp.rtr] n = rtrₙ)
              (hn  : n ∈ rtrₚ.nest.ids)
              (hm₁ : i₁ ∈ rtrₚ.prios.maximalsIn rtrₚ.muts.ids)
              (hm₂ : i₂ ∈ rtrₙ.prios.minimalsIn rtrₙ.rcns.ids)

end PrecGraph

notation i₁:max "<[" σ "]" i₂:max => PrecGraph.directPrecedence i₁ i₂ σ

variable {ι υ} [ID ι] [Value υ]

structure PrecGraph (σ : Reactor ι υ) where
  edges : Finset (ι × ι)
  wf : edges = { e : ι × ι | e.fst <[σ] e.snd }

noncomputable def PrecGraph.rcns {σ : Reactor ι υ} (π : PrecGraph σ) : ι ▸ Reaction ι υ := σ *[Cmp.rcn]