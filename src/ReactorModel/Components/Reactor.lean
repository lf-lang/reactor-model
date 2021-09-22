import ReactorModel.Components.Raw

open Ports

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Cmp
  | rtr
  | rcn
  | «mut»
  | prt (r : Ports.Role)
  | stateVar

variable {ι υ} [ID ι] [Value υ]

-- This is still WIP.
-- Cf. the big comment block below for an explanation.
def List.isRtrIDPathFor (i : ι) (ctx : Raw.Reactor ι υ) : Cmp → List ι → Prop
  | cmp, hd :: tl =>    ∃ ctx', (ctx.nest hd = some ctx') ∧ (tl.isRtrIDPathFor i ctx' cmp)
  | Cmp.rtr, [] =>      ∃ v, ctx.nest i = some v 
  | Cmp.rcn, [] =>      ∃ v, ctx.rcns i = some v
  | Cmp.mut, [] =>      ∃ v, ctx.muts i = some v
  | Cmp.prt r, [] =>    ∃ r, i ∈ (ctx.ports r).ids
  | Cmp.stateVar, [] => i ∈ ctx.state.ids

notation p " ~[" r "," c "] " i => List.isRtrIDPathFor i r c p

/-
`global` ensures ID-uniqueness within a component type between different reactors, 
i.e. no two distinct objects of the same component type can have the same ID.

Given a „context“ reactor ⊤, global ID-uniqueness is fulfilled if:
∀ (i : ι) (p₁ p₂ : ID-paths for i in ⊤), p₁ = p₂

An "ID-path" p for a given ID i is a finite sequence of reactor-IDs r₁, ..., rₙ such that
r₁ identifies some reactor x₁ in the nested network of ⊤, and all other rₘ in the sequence identify
a reactor in the nested network of xₘ₋₁, and xₙ contains some component identified by i (a port, reaction, mutation, or nested reactor).
Hence the sequence p = r₁, ..., rₙ is a path of IDs that leads us through the graph of nested reactors,
right to the reactor that contains the element identified by i.
Hence, a given ID i identifies an element in a reactor (including its nested networks) iff there exists an ID-path for it.

The condition of global  ID-uniqueness now simply requires that no two different IDs p₁ and p₂ can lead to the same ID 
(or as stated here, same IDs must have same paths).
Thus, even if we have two ports (e.g.) that live in completely different parts of the nested reactor tree, we ensure that they must
be identified by different IDs. 

What this uniqueness condition does not enforce is that IDs within the *same* reactor are all unique.
This is covered by `local`, which states that if an object of component type c with ID i is reached by a path p,
then that path can't lead to an object with ID i of a different component type c'.
That is, a reactor (uniquely identified by p) can't contain objects of different component types with the same ID.
-/
structure Raw.Reactor.uniqueIDs (rtr : Raw.Reactor ι υ) : Prop where
  global : ∀ i c p₁ p₂, (p₁ ~[rtr, c] i) → (p₂ ~[rtr, c] i) → p₁ = p₂  
  «local»: ∀ i c p, (p ~[rtr, c] i) → ¬∃ c', (c ≠ c') ∧ (p ~[rtr, c'] i)

-- The set of (defined) port IDs contained in a given reactor's nested network.
noncomputable def Raw.Reactor.nestedPortIDs (rtr : Raw.Reactor ι υ) (r : Ports.Role) : Set ι :=
  {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports r).ids}

structure Raw.Reactor.wellFormed' (rtr : Raw.Reactor ι υ) : Prop where
  mutsFinite :      { i | rtr.muts i ≠ none }.finite
  mutsTsSubInDeps : ∀ m i, rtr.muts i = some m → m.triggers ⊆ m.deps Role.in                                     
  mutsInDepOnly :   ∀ m i, rtr.muts i = some m → ∀ i i' s, (i =[m.deps Role.in] i') → m.body i s = m.body i' s    
  mutsOutDepOnly :  ∀ m i, rtr.muts i = some m → ∀ i s o, (o ∉ m.deps Role.out) → (m.body i s).prtVals[o] = none 
  rcnsFinite :      { i | rtr.rcns i ≠ none }.finite
  rtrWFMutDeps :    ∀ m r, rtr.muts i = some m → (m.deps r) ⊆ (rtr.ports r).ids -- ? ¯\_(ツ)_/¯                   
  rtrWFRcnDeps :    ∀ rcn i r, rtr.rcns i = some rcn → ↑(rcn.deps r) ⊆ ↑(rtr.ports r).ids ∪ (rtr.nestedPortIDs r.opposite)
  nestFiniteRtrs :  { i | rtr.nest i ≠ none }.finite
  uniqueIDs :       uniqueIDs rtr

-- Recursive step for wellFormed'.
def Raw.Reactor.wellFormed (rtr : Raw.Reactor ι υ) : Prop :=
  rtr.wellFormed' -- ∧ (∀ r : Raw.Reactor ι υ, r ∈ rtr.nest.rtrs.values → r.wellFormed)

structure Reactor (ι υ) [ID ι] [Value υ] where 
  raw : Raw.Reactor ι υ
  wf : raw.wellFormed  

namespace Reactor

-- These are the "tivial" accessors on `Reactor` - i.e. those that don't (barely) involve 
-- the constraints given by `Reactor.wf`. The non-trivial accessors are defined in the files
-- where the corresponding components are defined (`Mutation`).

def ports (rtr : Reactor ι υ) : Ports.Role → Ports ι υ := rtr.raw.ports
def state (rtr : Reactor ι υ) : StateVars ι υ          := rtr.raw.state
def rcns  (rtr : Reactor ι υ) : ι ▸ Reaction ι υ       := {lookup := rtr.raw.rcns, finite := rtr.wf.rcnsFinite}
def prios (rtr : Reactor ι υ) : PartialOrder ι         := rtr.raw.prios
def nest  (rtr : Reactor ι υ) : ι ▸ Reactor ι υ        := {lookup := rtr.raw.nest, finite := rtr.wf.nestFiniteRtrs : Finmap ι (Raw.Reactor ι υ)}.map (λ r => {raw := r, wf := sorry})

end Reactor

-- TODO: Lift the `wellFormed` properties (as new theorems) to not be about `Raw` components anymore.
