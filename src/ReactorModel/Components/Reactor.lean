import ReactorModel.Components.Raw
import ReactorModel.Mathlib

open Ports

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
-- These are used heavily for accessing objects in a reactor (cf. Components/Accessors.lean).
inductive Cmp
  | rtr
  | rcn
  | prt
  | stv -- State variable

variable {ι υ} [ID ι] [Value υ]

namespace Raw.Reactor

-- This relation expresses whether a given list of identifiers forms a path
-- that starts at the given top-level (raw) reactor (`σ`) and successively
-- identifies all of the nested (raw) reactors required to reach a given
-- component (of a given component type) identified by identifier `i`.
-- 
-- We use this relation to ensure ID-uniqueness in reactors (cf. `uniqueIDs` below).
--
-- Technicalities:
-- If a reactor-ID-path `p` for a given ID `i` is a finite sequence of reactor-IDs `r₁, ..., rₙ`,
-- then `r₁` identifies some reactor `x₁` in the nested network of `σ`, and all other `rₘ` in the
-- sequence identify a reactor in the nested network of `xₘ₋₁`, and `xₙ` contains some component
-- identified by `i` (a port, state variable, reaction, or nested reactor).
--
-- The notation `p ~[σ, cmp] i` is used to express that list `p` forms a path
-- through `σ` that reaches component `i` of component type `cmp`.
def isRtrIDPathFor (i : ι) (σ : Raw.Reactor ι υ) : Cmp → List ι → Prop
  | cmp, hd :: tl => ∃ σ', (σ.nest hd = some σ') ∧ (isRtrIDPathFor i σ' cmp tl)
  | Cmp.rtr,   [] => ∃ v, σ.nest i = some v 
  | Cmp.rcn,   [] => ∃ v, σ.rcns i = some v
  | Cmp.prt,   [] => i ∈ σ.ports.ids 
  | Cmp.stv,   [] => i ∈ σ.state.ids 

notation p:max " ~[" r:max ", " c:max "] " i => isRtrIDPathFor i r c p

-- The `uniqueIDs` proposition states that all components in a given (raw) reactor
-- that are identifiable by IDs (`ι`) have unique IDs.
--
-- The `external` proposition ensures ID-uniqueness within *one class of components*
-- (same component type), but between *different reactors*. That is, no two distinct
-- objects of the same component type can have the same ID.
-- This is achieved by stating that if there are two reactor-ID-paths that lead to
-- the same identifier, then those paths must be the same. 
--
-- The `internal` proposition ensures ID-uniqueness within *one reactor*, but between
-- *different types of components*. That is, no two distinct objects in a reactor can
-- have the same ID.
-- This is achieved by stating that if a reactor-ID-path `p` leads to an identifier `i` 
-- that identifies an object of some component type `c`, then path `p` can't also lead
-- an ID `i` that identifies some other component type.
structure uniqueIDs (σ : Raw.Reactor ι υ) : Prop where
  external : ∀ {i c p₁ p₂}, (p₁ ~[σ, c] i) → (p₂ ~[σ, c] i) → p₁ = p₂  
  internal : ∀ {i p c₁ c₂}, (p ~[σ, c₁] i) → (p ~[σ, c₂] i) → c₁ = c₂ 

end Raw.Reactor

-- These are the constraints required for a "proper" reaction.
-- For more information cf. `Reaction`.
structure Raw.Reaction.wellFormed (rcn : Raw.Reaction ι υ) : Prop where
  triggersSubInDeps : rcn.triggers ⊆ rcn.deps Role.in                                     
  outDepOnly :        ∀ i s {o} (v : υ), (o ∉ rcn.deps Role.out) → (Change.port o v) ∉ (rcn.body i s)
  normNoChild :       rcn.isNorm → rcn.children = ∅

namespace Raw.Reactor

-- These are the (almost all of the) constraints required for a "proper" reactor.
-- These constraints only directly constrain the given reactor, and don't apply
-- to the nested reactors (this is done in `wellFormed` below).
--
-- Since these constraints are still a WIP, we won't comment on them further yet.
structure directlyWellFormed (rtr : Raw.Reactor ι υ) : Prop where
  rcnsFinite :      { i | rtr.rcns i ≠ none }.finite
  nestFiniteRtrs :  { i | rtr.nest i ≠ none }.finite
  rcnsWF :          ∀ {rcn}, (∃ i, rtr.rcns i = some rcn) → rcn.wellFormed
  wfRoles :         rtr.roles.ids = rtr.ports.ids
  wfNormDeps :      ∀ n i r, rtr.rcns i = some n → n.isNorm → ↑(n.deps r) ⊆ ↑(rtr.ports' r).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' r.opposite).ids}
  wfMutDeps :       ∀ m i, rtr.rcns i = some m → m.isMut → (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (↑(m.deps Role.out) ⊆ ↑(rtr.ports' Role.out).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' Role.in).ids})
  wfMutChildren :   ∀ m i, rtr.rcns i = some m → m.isMut → ↑m.children ⊆ { i | rtr.nest i ≠ none }
  mutsBeforeNorms : ∀ iₙ iₘ n m, rtr.rcns iᵣ = some n → rtr.rcns i = some m → n.isNorm → m.isMut → rtr.prios.lt iₘ iₙ
  mutsLinearOrder : ∀ i₁ i₂ m₁ m₂, rtr.rcns i₁ = some m₁ → rtr.rcns i₂ = some m₂ → m₁.isMut → m₂.isMut → (rtr.prios.le i₁ i₂ ∨ rtr.prios.le i₂ i₁)
  uniqueIDs :       uniqueIDs rtr  

-- To define properties of reactors recursively, we need a concept of containment.
-- That is, that a reactor is contained in a different reactor.
-- We do this as a transitive closure of a direct containment relation.
-- Thus, we first define what it means for a (raw) reactor to be contained directly
-- in a different reactor. Then define a transitive step on the direct containment.
inductive isStrictlyContainedIn : (Raw.Reactor ι υ) → (Raw.Reactor ι υ) → Prop 
  | direct {child parent : Raw.Reactor ι υ} : (∃ i, parent.nest i = child) → isStrictlyContainedIn child parent
  | trans {r₁ r₂ r₃ : Raw.Reactor ι υ} : (isStrictlyContainedIn r₁ r₂) → (isStrictlyContainedIn r₂ r₃) → (isStrictlyContainedIn r₁ r₃)

-- Having defined well-formedness for a single reactor we proceed to extend this to a full reactor.
-- A reactor is well-formed if all the proerties above hold for itself as well as all its contained reactors.
structure wellFormed (σ : Raw.Reactor ι υ) : Prop where
  direct : σ.directlyWellFormed 
  contained : ∀ {rtr : Raw.Reactor ι υ}, rtr.isStrictlyContainedIn σ → rtr.directlyWellFormed

end Raw.Reactor

-- A `Reactor` is a raw reactor that is also well-formed.
-- We do this using a structure to be able to access the structure and 
-- the well-formedness properties separately.
structure Reactor (ι υ) [ID ι] [Value υ] where 
  raw : Raw.Reactor ι υ
  wf : raw.wellFormed  

-- The containement relation lifted for "proper" reactors.
def Reactor.isStrictlyContainedIn : (Reactor ι υ) → (Reactor ι υ) → Prop := 
  λ child parent => child.raw.isStrictlyContainedIn parent.raw

theorem Raw.Reactor.isStrictlyContainedIn_preserves_wf
  {rtr rtr' : Raw.Reactor ι υ} (hc : rtr'.isStrictlyContainedIn rtr) (hw : rtr.wellFormed) :
  rtr'.wellFormed := {
    direct := hw.contained hc,
    contained := λ hr => hw.contained (isStrictlyContainedIn.trans hr hc) 
  }

-- Lifted versions of the "tivial" accessors on `Reactor` - i.e. those that don't
-- (or only barely) involve the constraints given by `Reactor.wf`.
-- The only non-trivial accessor is `rcns` defined in Components/Reaction.lean.
namespace Reactor

def ports (rtr : Reactor ι υ) : Ports ι υ       := rtr.raw.ports
def roles (rtr : Reactor ι υ) : ι ▸ Ports.Role  := rtr.raw.roles
def state (rtr : Reactor ι υ) : StateVars ι υ   := rtr.raw.state
def prios (rtr : Reactor ι υ) : PartialOrder ι  := rtr.raw.prios

-- The `nest` accessor lifted to return a finmap of "proper" reactors.
-- 
-- We're doing two lifting steps at once here:
-- 1. We turn `rtr.raw.nest` into a finmap that has raw reactors as values.
-- 2. We map on that finmap to get a finmap that returns "proper" reactors.
def nest (rtr : Reactor ι υ) : ι ▸ Reactor ι υ := 
  let raw : Finmap ι (Raw.Reactor ι υ) := { lookup := rtr.raw.nest, finite := rtr.wf.direct.nestFiniteRtrs }
  raw.map' (λ r h => {
    raw := r, 
    wf := by
      have hm := Finmap.values_def.mp h
      have h' := Raw.Reactor.isStrictlyContainedIn.direct hm
      exact Raw.Reactor.isStrictlyContainedIn_preserves_wf h' rtr.wf
  })

-- An accessor for ports, that allows us to separate them by port role.
noncomputable def ports' (rtr : Reactor ι υ) : Ports.Role → Ports ι υ := rtr.raw.ports'

end Reactor

-- TODO: Lift the `wellFormed` properties (as new theorems) to not be about `Raw` components anymore.
