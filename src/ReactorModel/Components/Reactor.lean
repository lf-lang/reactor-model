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

/-
To define properties of reactors recursively, we need the concept of containment.
That is, that a reactor is contained in a different reactor.
We do this as a transitive closure of a direct containment relation.
Thus, we first define what it means for a (raw) reactor to be contained directly
in a different reactor.
-/
def Raw.isContainedDirectlyIn (rtr rtr' : Raw.Reactor ι υ) : Prop :=
 ∃ i, rtr'.nest.rtrs i = some rtr

/-
This direct containment we can then extend through a
reflexive, transitive closure, as an inductively defined proposition.

We need to be explicit about the variables ι and υ and their instances here,
so that the typechecker can get things through the `multi` closure from Relations.
-/
def Raw.isContainedIn := Relations.multi (X := Raw.Reactor ι υ) (Raw.isContainedDirectlyIn )

def Raw.isContainedIn_refl (rtr : Raw.Reactor ι υ)  :=
 @Relations.multi.multi_refl (Raw.isContainedDirectlyIn) rtr --some universes stuff...

-- The set of (defined) port IDs contained in a given reactor's nested network.
noncomputable def Raw.Reactor.nestedPortIDs (rtr : Raw.Reactor ι υ) (r : Ports.Role) : Set ι :=
  {i | ∃ j x, rtr.nest.rtrs j = some x ∧ i ∈ (x.ports r).ids}
/-
Note that this only defines the PortIDs one 'level' down the chain of reactors. We dissalow that we have e.g.:
∃ j k x, (rtr.nest.rtrs j).nest.rtrs.k = some x ∧ i ∈ (x.ports r).ids

We should double-check this with the CyPhy paper/Marten's thesis and the LF implementation.
Alteratively we would write:

  {i | ∃ rtr', Raw.isContainedIn rtr' rtr ∧ i ∈ (rtr'.ports r).ids}

-/

-- We can now proceed to define well-formedness in (raw) reactors. We start by defining the properties of a single reactor
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

/-
Having defined well-formedness for a single reactor we proceed to extend this to a full reactor.
A reactor is well-formed if all the proerties above hold for itself as well as all its contained reactors.
-/

structure Raw.Reactor.wellFormed (rtr : Raw.Reactor ι υ) : Prop where
  selfWf : rtr.wellFormed' 
  containedWF : ∀ r : Raw.Reactor ι υ, Raw.isContainedIn r rtr → r.wellFormed'

/-
We can now finally define a (proper) Reactor:
A Reactor is a raw Reactor that is also well-formed.
We do this using a structure to be able to access the structure and
their properties separately.
-/
structure Reactor (ι υ) [ID ι] [Value υ] where 
  raw : Raw.Reactor ι υ
  wf : raw.wellFormed  

namespace Reactor

/-
We can also define ('lift') the containement relation for these 'proper' reactors:
-/
def isContainedDirectlyIn (rtr rtr' : Reactor ι υ) : Prop :=
 Raw.isContainedDirectlyIn rtr.raw rtr'.raw

def isContainedIn {ι υ : Type} {inst₁ : ID ι} {inst₂ : Value υ} := Relations.multi (@isContainedDirectlyIn ι υ inst₁ inst₂)
/-
The main property of reactors is that a contained reactor is also well-formed.
-/
lemma Raw.isContainedDirectlyInPreservesWF (rtr rtr' : Raw.Reactor ι υ) : 
  Raw.isContainedDirectlyIn rtr' rtr ∧ rtr.wellFormed → rtr'.wellFormed := by
  intros Hdisj
  have Hcontwf := Hdisj.2.containedWF 
  have Hdirectly := Hdisj.1 -- can I do this with a pattern directly at intros?
  have Hrefl := (Relations.multi.multi_refl Raw.isContainedDirectlyIn rtr')
  have Hcont : Relations.multi.multi_step Raw.isContainedDirectlyIn rtr rtr' rtr' (Hdisj.1) 
     



theorem Raw.isContainedInPreservesWF (rtr rtr' : Raw.Reactor ι υ) : 
  Raw.isContainedIn rtr' rtr ∧ rtr.wellFormed → rtr'.wellFormed := by
  intros Hdisj
  have Hcont := Hdisj.1
  have Hrwf := Hdisj.2 --can I do this with a pattern directly at intros?
  induction Hcont with
  | multi_refl => assumption
  | multi_step => 
    


-- These are the "tivial" accessors on `Reactor` - i.e. those that don't (barely) involve 
-- the constraints given by `Reactor.wf`. The non-trivial accessors are defined in the files
-- where the corresponding components are defined (`Mutation` and `Network`).

def ports (rtr : Reactor ι υ) : Ports.Role → Ports ι υ := rtr.raw.ports
def state (rtr : Reactor ι υ) : StateVars ι υ          := rtr.raw.state
def rcns  (rtr : Reactor ι υ) : ι ▸ Reaction ι υ       := {lookup := rtr.raw.rcns, finite := rtr.wf.selfWf.rcnsFinite} 
def prios (rtr : Reactor ι υ) : PartialOrder ι         := rtr.raw.prios

end Reactor

-- TODO: Lift the `wellFormed` properties (as new theorems) to not be about `Raw` components anymore.
