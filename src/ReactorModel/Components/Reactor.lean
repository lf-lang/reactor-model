import ReactorModel.Components.Raw

open Reactor
open Reactor.Ports

variable {ι υ} [ID ι] [Value υ]

def List.isRtrIDPathFor (i : ι) (ctx : Raw.Reactor ι υ) : List ι → Prop
  | hd :: tl => ∃ ctx', (ctx.nest.rtrs hd = some ctx') ∧ (tl.isRtrIDPathFor i ctx')
  | [] => 
    (∃ r, i ∈ (ctx.ports r).ids) ∨ 
    (i ∈ ctx.state.ids) ∨
    (i ∈ ctx.rcns.ids) ∨ 
    (i ∈ ctx.muts.ids) ∨ 
    (i ∈ ctx.nest.rtrs.ids)

notation p " *ᵣ[" r "] " i => List.isRtrIDPathFor i r p

noncomputable def Raw.Reactor.nestedPortIDs (rtr : Raw.Reactor ι υ) (r : Ports.Role) : Finset ι :=
  rtr.nest.rtrs.values.bUnion (λ x => (x.ports r).ids)

structure Raw.Reactor.wellFormed' (rtr : Raw.Reactor ι υ) : Prop where
  mutsTsSubInDeps : ∀ m,       m ∈ rtr.muts.values → m.triggers ⊆ m.deps Role.in                                     
  mutsInDepOnly :   ∀ m,       m ∈ rtr.muts.values → ∀ i i' s, (i =[m.deps Role.in] i') → m.body i s = m.body i' s    
  mutsOutDepOnly :  ∀ m,       m ∈ rtr.muts.values → ∀ i s o, (o ∉ m.deps Role.out) → (m.body i s).prtVals[o] = none 
  rtrWFMutDeps :    ∀ m r,     m ∈ rtr.muts.values → (m.deps r) ⊆ (rtr.ports r).ids -- ? ¯\_(ツ)_/¯                   
  rtrWFRcnDeps :    ∀ rcn r, rcn ∈ rtr.rcns.values → (rcn.deps r) ⊆ (rtr.ports r).ids ∪ (rtr.nestedPortIDs r.opposite)
  nestWFCns :       ∀ c,       c ∈ rtr.nest.cns → (c.src ∈ rtr.nestedPortIDs Role.out) ∧ (c.dst ∈ rtr.nestedPortIDs Role.in)
  wfIDs :           ∀ i₁ i₂ p₁ p₂, (p₁ *ᵣ[rtr] i₁) → (p₂ *ᵣ[rtr] i₂) → i₁ = i₂ → p₁ = p₂

/-
`wfIDs` ensures ID-uniqueness, i.e. no two distinct instances of the component can have the same ID.

Given a „context“ reactor ⊤, ID-uniqueness is fulfilled if:
∀ (i₁ i₂ : ι) (p₁ p₂ : ID-paths for i₁ and i₂ in ⊤), i₁ = i₂ → p₁ = p₂

An "ID-path" p for a given ID i is a finite sequence of reactor-IDs r₁, ..., rₙ such that
r₁ identifies some reactor x₁ in the nested network of ⊤, and all other rₘ in the sequence identify
a reactor in the nested network of xₘ₋₁, and xₙ contains some component identified by i (a port, reaction, mutation, or nested reactor).
Hence the sequence p = r₁, ..., rₙ is a path of IDs that leads us through the graph of nested reactors,
right to the reactor that contains the element identified by i.
Hence, a given ID i identifies an element in a reactor (including its nested networks) iff there exists an ID-path for it.

The condition of ID-uniqueness now simply requires that no two different IDs p₁ and p₂ can lead to the same ID 
(or as stated here, same IDs must have same paths).
Thus, even if we have two ports (e.g.) that live in completely different parts of the nested reactor tree, we ensure that they must
be identified by different IDs. 

What this uniqueness condition does not enforce is that IDs within the *same* reactor are all unique.
In fact, by the definition of ID-paths, they must all have the same ID-path.
This isn't an issue though, because
(1) We're not actually interested in making sure that different kinds of components have non overlapping IDs.
    E.g. it's ok for a port to have the same ID as a mutation, because we will always have to know which kind of object we're trying to access anyway.
(2) *Within* a reactor, IDs of the same component-type can't overlap. 
    E.g. mutations (`muts`) are defined as a `Finmap`, which ensures that each valid mutation-ID refers to a unique `Mutation`.
-/

-- Recursive step for wellFormed'.
def Raw.Reactor.wellFormed (rtr : Raw.Reactor ι υ) : Prop :=
  rtr.wellFormed' -- ∧ (∀ r : Raw.Reactor ι υ, r ∈ rtr.nest.rtrs.values → r.wellFormed)

structure Reactor (ι υ) [ID ι] [Value υ] where 
  raw : Raw.Reactor ι υ
  wf : raw.wellFormed  

namespace Reactor

def ports (rtr : Reactor ι υ) : Ports.Role → Ports ι υ := rtr.raw.ports
def state (rtr : Reactor ι υ) : StateVars ι υ          := rtr.raw.state
def rcns  (rtr : Reactor ι υ) : ι ▸ Reaction ι υ       := rtr.raw.rcns
def prios (rtr : Reactor ι υ) : PartialOrder ι         := rtr.raw.prios

end Reactor

-- Lift the `wellFormed` properties (as new theorems) to not be about `Raw` components anymore.
