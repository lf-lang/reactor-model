import ReactorModel.Components.Raw

open Ports

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Cmp
  | rtr
  | rcn
  | prt
  | stv -- state var

variable {ι υ} [ID ι] [Value υ]

-- Cf. the big comment block below for an explanation.
def List.isRtrIDPathFor (i : ι) (ctx : Raw.Reactor ι υ) : Cmp → List ι → Prop
  | cmp, hd :: tl => ∃ ctx', (ctx.nest hd = some ctx') ∧ (tl.isRtrIDPathFor i ctx' cmp)
  | Cmp.rtr,   [] => ∃ v, ctx.nest i = some v 
  | Cmp.rcn,   [] => ∃ v, ctx.rcns i = some v
  | Cmp.prt,   [] => i ∈ ctx.ports.ids 
  | Cmp.stv,   [] => i ∈ ctx.state.ids 

notation p:max " ~[" r:max ", " c:max "] " i => List.isRtrIDPathFor i r c p

namespace Raw.Reactor

/-
`external` ensures ID-uniqueness within a component type between different reactors, 
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
This is covered by `internal`, which states that if an object of component type c with ID i is reached by a path p,
then that path can't lead to an object with ID i of a different component type c'.
That is, a reactor (uniquely identified by p) can't contain objects of different component types with the same ID.
-/
structure uniqueIDs (rtr : Raw.Reactor ι υ) : Prop where
  external : ∀ i c p₁ p₂, (p₁ ~[rtr, c] i) → (p₂ ~[rtr, c] i) → p₁ = p₂  
  internal : ∀ i c p, (p ~[rtr, c] i) → ¬∃ c', (c ≠ c') ∧ (p ~[rtr, c'] i)

structure rcnIsWF (rcn : Raw.Reaction ι υ) : Prop where
  rcnsTsSubInDeps : rcn.triggers ⊆ rcn.deps Role.in                                     
  rcnsInDepOnly :   ∀ i i' s, (i =[rcn.deps Role.in] i') → (rcn.body i s = rcn.body i' s)    
  rcnsOutDepOnly :  ∀ i s o (v : υ), (o ∉ rcn.deps Role.out) → (Change.port o v) ∉ (rcn.body i s)

structure wellFormed' (rtr : Raw.Reactor ι υ) : Prop where
  rcnsFinite :      { i | rtr.rcns i ≠ none }.finite
  nestFiniteRtrs :  { i | rtr.nest i ≠ none }.finite
  rcnsWF :          ∀ rcn i, rtr.rcns i = some rcn → rcnIsWF rcn
  wfRoles :         rtr.roles.ids = rtr.ports.ids
  wfNormDeps :      ∀ n i r, rtr.rcns i = some n → n.isNorm → ↑(n.deps r) ⊆ ↑(rtr.ports' r).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' r.opposite).ids}
  wfMutDeps :       ∀ m i, rtr.rcns i = some m → m.isMut → (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (↑(m.deps Role.out) ⊆ ↑(rtr.ports' Role.out).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' Role.in).ids})
  mutsBeforeNorms : ∀ iₙ iₘ n m, rtr.rcns iᵣ = some n → rtr.rcns i = some m → n.isNorm → m.isMut → rtr.prios.lt iₘ iₙ
  mutsLinearOrder : ∀ i₁ i₂ m₁ m₂, rtr.rcns i₁ = some m₁ → rtr.rcns i₂ = some m₂ → m₁.isMut → m₂.isMut → (rtr.prios.le i₁ i₂ ∨ rtr.prios.le i₂ i₁)
  uniqueIDs :       uniqueIDs rtr  

-- Recursive step for wellFormed'.
def wellFormed (rtr : Raw.Reactor ι υ) : Prop := 
  rtr.wellFormed' -- TODO: ∧ (∀ r : Raw.Reactor ι υ, r ∈ rtr.nest.rtrs.values → r.wellFormed)

end Raw.Reactor

structure Reactor (ι υ) [ID ι] [Value υ] where 
  raw : Raw.Reactor ι υ
  wf : raw.wellFormed  

namespace Reactor

-- These are the "tivial" accessors on `Reactor` - i.e. those that don't (barely) involve 
-- the constraints given by `Reactor.wf`. The non-trivial accessors are defined in the files
-- where the corresponding components are defined (`Reaction`).

def ports (rtr : Reactor ι υ) : Ports ι υ       := rtr.raw.ports
def roles (rtr : Reactor ι υ) : ι ▸ Ports.Role  := rtr.raw.roles
def state (rtr : Reactor ι υ) : StateVars ι υ   := rtr.raw.state
def nest  (rtr : Reactor ι υ) : ι ▸ Reactor ι υ := {lookup := rtr.raw.nest, finite := rtr.wf.nestFiniteRtrs : Finmap ι (Raw.Reactor ι υ)}.map (λ r => {raw := r, wf := sorry})
def prios (rtr : Reactor ι υ) : PartialOrder ι  := rtr.raw.prios

noncomputable def ports' (rtr : Reactor ι υ) : Ports.Role → Ports ι υ := rtr.raw.ports'

end Reactor

-- TODO: Lift the `wellFormed` properties (as new theorems) to not be about `Raw` components anymore.
