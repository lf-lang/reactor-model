import ReactorModel.Components.Raw

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
-- We use this relation in `IDPath` to ensure ID-uniqueness in reactors
-- (cf. `uniqueIDs` below).
--
-- Technicalities:
-- If a reactor-ID-path `p` for a given ID `i` is a finite sequence of reactor-IDs `r₁, ..., rₙ`,
-- then `r₁` identifies some reactor `x₁` in the nested network of `σ`, and all other `rₘ` in the
-- sequence identify a reactor in the nested network of `xₘ₋₁`, and `xₙ` contains some component
-- identified by `i` (a port, state variable, reaction, or nested reactor).
inductive IDPath : Raw.Reactor ι υ → ι → Type _ 
  | rtr σ i : σ.nest i ≠ none → IDPath σ i
  | rcn σ i : σ.rcns i ≠ none → IDPath σ i
  | prt σ i : i ∈ σ.ports.ids → IDPath σ i
  | stv σ i : i ∈ σ.state.ids → IDPath σ i
  | nest (σ : Raw.Reactor ι υ) {σ'} (i i') : (IDPath σ' i) → (σ.nest i' = some σ') → IDPath σ i

end Raw.Reactor

-- These are the constraints required for a "proper" reaction.
-- For more information cf. `Reaction`.
structure Raw.Reaction.wellFormed (rcn : Raw.Reaction ι υ) : Prop where
  tsSubInDeps : rcn.triggers ⊆ rcn.deps Role.in                                     
  outDepOnly :  ∀ i s {o} (v : υ), (o ∉ rcn.deps Role.out) → (Change.port o v) ∉ (rcn.body i s)
  normNoChild : rcn.isNorm → rcn.children = ∅

namespace Raw.Reactor

-- These are the (almost all of the) constraints required for a "proper" reactor.
-- These constraints only directly constrain the given reactor, and don't apply
-- to the nested reactors (this is done in `wellFormed` below).
--
-- Since these constraints are still a WIP, we won't comment on them further yet.
structure directlyWellFormed (rtr : Raw.Reactor ι υ) : Prop where
  uniqueIDs :       ∀ p₁ p₂ : IDPath rtr i, p₁ = p₂ 
  rcnsWF :          ∀ {rcn}, (∃ i, rtr.rcns i = some rcn) → rcn.wellFormed
  rcnsFinite :      { i | rtr.rcns i ≠ none }.finite
  nestFiniteRtrs :  { i | rtr.nest i ≠ none }.finite
  wfRoles :         rtr.roles.ids = rtr.ports.ids
  wfNormDeps :      ∀ n i r, rtr.rcns i = some n → n.isNorm → ↑(n.deps r) ⊆ ↑(rtr.ports' r).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' r.opposite).ids}
  wfMutDeps :       ∀ m i, rtr.rcns i = some m → m.isMut → (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (↑(m.deps Role.out) ⊆ ↑(rtr.ports' Role.out).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' Role.in).ids})
  mutsBeforeNorms : ∀ iₙ iₘ, (∃ n, rtr.rcns iₙ = some n ∧ n.isNorm) → (∃ m, rtr.rcns iₘ = some m ∧ m.isMut) → rtr.prios.lt iₘ iₙ
  mutsLinearOrder : ∀ i₁ i₂ m₁ m₂, rtr.rcns i₁ = some m₁ → rtr.rcns i₂ = some m₂ → m₁.isMut → m₂.isMut → (rtr.prios.le i₁ i₂ ∨ rtr.prios.le i₂ i₁) 

-- To define properties of reactors recursively, we need a concept of containment.
-- That is, that a reactor is contained in a different reactor.
-- We do this as a transitive closure of a direct containment relation.
-- Thus, we first define what it means for a (raw) reactor to be contained directly
-- in a different reactor. Then define a transitive step on the direct containment.
inductive isAncestorOf : (Raw.Reactor ι υ) → (Raw.Reactor ι υ) → Prop 
  | nested {parent child i} : (parent.nest i = some child) → isAncestorOf parent child
  | creatable {old new rcn p s i iᵣ} : (old.rcns i = some rcn) → (Change.create new iᵣ ∈ rcn.body p s) → isAncestorOf old new
  | trans {r₁ r₂ r₃} : (isAncestorOf r₁ r₂) → (isAncestorOf r₂ r₃) → (isAncestorOf r₁ r₃)

-- Having defined well-formedness for a single reactor we proceed to extend this to a full reactor
-- hierarchy. A reactor is well-formed if all the properties above hold for itself as well as all
-- its contained and creatable reactors. 
structure wellFormed (σ : Raw.Reactor ι υ) : Prop where
  direct : σ.directlyWellFormed 
  offspring : ∀ {rtr : Raw.Reactor ι υ}, σ.isAncestorOf rtr → rtr.directlyWellFormed

end Raw.Reactor

-- A `Reactor` is a raw reactor that is also well-formed.
-- We do this using a structure to be able to access the structure and 
-- the well-formedness properties separately.
@[ext]
structure Reactor (ι υ) [ID ι] [Value υ] where 
  raw : Raw.Reactor ι υ
  rawWF : raw.wellFormed  

theorem Raw.Reactor.isAncestorOf_preserves_wf
  {rtr₁ rtr₂ : Raw.Reactor ι υ} (ha : rtr₁.isAncestorOf rtr₂) (hw : rtr₁.wellFormed) :
  rtr₂.wellFormed := {
    direct := hw.offspring ha,
    offspring := λ hr => hw.offspring (isAncestorOf.trans ha hr)
  }