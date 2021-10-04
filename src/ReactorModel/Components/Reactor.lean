import ReactorModel.Components.Raw
import ReactorModel.Relations

open Ports

variable {ι υ} [ID ι] [Value υ]

-- This is still WIP.
-- Cf. the big comment block below for an explanation.
def List.isRtrIDPathFor (i : ι) (ctx : Raw.Reactor ι υ) : List ι → Prop
  | hd :: tl => ∃ ctx', (ctx.nest.rtrs hd = some ctx') ∧ (tl.isRtrIDPathFor i ctx')
  | [] => 
    (∃ r, i ∈ (ctx.ports r).ids) ∨ 
    (i ∈ ctx.state.ids) ∨
    (∃ v, ctx.rcns i = some v) ∨ 
    (∃ v, ctx.muts i = some v) ∨ 
    (∃ v, ctx.nest.rtrs i = some v)

notation p " *ᵣ[" r "] " i => List.isRtrIDPathFor i r p

-- The set of (defined) port IDs contained in a given reactor's nested network.
noncomputable def Raw.Reactor.nestedPortIDs (rtr : Raw.Reactor ι υ) (r : Ports.Role) : Set ι :=
  {i | ∃ j x, rtr.nest.rtrs j = some x ∧ i ∈ (x.ports r).ids}

/-
To define properties of reactors recursively, we need the concept of containment.
That is, that a reactor is contained in a different reactor.
We do this as a transitive closure of a direct containment relation.
Thus, we first define what it means for a (raw) reactor to be contained directly
in a different reactor.
-/
def containedDirectlyIn (rtr rtr' : Raw.Reactor ι υ) : Prop :=
 ∃ i, rtr'.nest.rtrs i = some rtr

/-
This direct containment we can then extend through a
reflexive, transitive closure, as an inductively defined proposition:
-/
def containedIn := Relations.multi containedDirectlyIn

structure Raw.Reactor.wellFormed' (rtr : Raw.Reactor ι υ) : Prop where
  mutsFinite :      { i | rtr.muts i ≠ none }.finite
  mutsTsSubInDeps : ∀ m i, rtr.muts i = some m → m.triggers ⊆ m.deps Role.in                                     
  mutsInDepOnly :   ∀ m i, rtr.muts i = some m → ∀ i i' s, (i =[m.deps Role.in] i') → m.body i s = m.body i' s    
  mutsOutDepOnly :  ∀ m i, rtr.muts i = some m → ∀ i s o, (o ∉ m.deps Role.out) → (m.body i s).prtVals[o] = none 
  rcnsFinite :      { i | rtr.rcns i ≠ none }.finite
  rtrWFMutDeps :    ∀ m r, rtr.muts i = some m  → (m.deps r) ⊆ (rtr.ports r).ids -- ? ¯\_(ツ)_/¯                   
  rtrWFRcnDeps :    ∀ rcn i r, rtr.rcns i = some rcn → ↑(rcn.deps r) ⊆ ↑(rtr.ports r).ids ∪ (rtr.nestedPortIDs r.opposite)
  nestFiniteRtrs :  { i | rtr.nest.rtrs i ≠ none }.finite
  nestWFCns :       ∀ c, c ∈ rtr.nest.cns → (c.src ∈ rtr.nestedPortIDs Role.out) ∧ (c.dst ∈ rtr.nestedPortIDs Role.in)
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
  rtr.wellFormed' ∧ (∀ r : Raw.Reactor ι υ, ∃ i, r ∈ rtr.nest.rtrs → r.wellFormed')

structure Reactor (ι υ) [ID ι] [Value υ] where 
  raw : Raw.Reactor ι υ
  wf : raw.wellFormed  

namespace Reactor

-- These are the "tivial" accessors on `Reactor` - i.e. those that don't (barely) involve 
-- the constraints given by `Reactor.wf`. The non-trivial accessors are defined in the files
-- where the corresponding components are defined (`Mutation` and `Network`).

def ports (rtr : Reactor ι υ) : Ports.Role → Ports ι υ := rtr.raw.ports
def state (rtr : Reactor ι υ) : StateVars ι υ          := rtr.raw.state
def rcns  (rtr : Reactor ι υ) : ι ▸ Reaction ι υ       := {lookup := rtr.raw.rcns, finite := rtr.wf.rcnsFinite}
def prios (rtr : Reactor ι υ) : PartialOrder ι         := rtr.raw.prios

end Reactor

-- TODO: Lift the `wellFormed` properties (as new theorems) to not be about `Raw` components anymore.
