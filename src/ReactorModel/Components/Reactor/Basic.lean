import ReactorModel.Components.Raw

open Ports

variable {ι υ} [Value υ]

-- Cf. `Reactor.Lineage`.
inductive Raw.Reactor.Lineage : Raw.Reactor ι υ → ι → Type _ 
  | rtr σ i : σ.nest i ≠ none → Lineage σ i
  | rcn σ i : σ.rcns i ≠ none → Lineage σ i
  | prt σ i : i ∈ σ.ports.ids → Lineage σ i
  | stv σ i : i ∈ σ.state.ids → Lineage σ i
  | nest (σ : Raw.Reactor ι υ) {σ'} (i i') : (Lineage σ' i) → (σ.nest i' = some σ') → Lineage σ i

-- These are the constraints required for a "proper" reaction.
-- They are used in `Reaction.fromRaw` to lift a `Raw.Reaction` to a
-- "proper" `Reaction`.
structure Raw.Reaction.wellFormed (rcn : Raw.Reaction ι υ) : Prop where
  tsSubInDeps : rcn.triggers ⊆ rcn.deps Role.in                                     
  outDepOnly :  ∀ i s {o} (v : υ), (o ∉ rcn.deps Role.out) → (Change.port o v) ∉ (rcn.body i s)
  normNoChild : rcn.isNorm → rcn.children = ∅

namespace Raw.Reactor

-- These are the (almost all of the) constraints required for a "proper" reactor.
-- These constraints only directly constrain the given reactor, and don't apply
-- to the reactors nested in it or created by it (via a mutation). 
-- The latter cases are covered in `wellFormed` below.
--
-- The constraints can be separated into three different categories
-- 1. Reaction constraints (`rcnsWF`)
-- 2. ID constraints (`uniqueIDs`)
-- 3. Reactor constraints (all others)
--
-- Note that some constraints are quite complicated in their type.
-- This is because they're defined over `Raw` components for which
-- we don't (want to) declare many conveniences. Categories 2 and 3
-- are lifted in Components>Reactor>Properties.lean, which will "clean
-- up" their types as well.
-- 
-- These constraints play an important role in limiting the behavior of
-- reactors and are thus partially responsible for its determinism. They
-- are therefore subject to change, as the need for different/more
-- constraints may arise.
structure directlyWellFormed (rtr : Raw.Reactor ι υ) : Prop where
  uniqueIDs :       ∀ l₁ l₂ : Lineage rtr i, l₁ = l₂ 
  rcnsWF :          ∀ {rcn}, (∃ i, rtr.rcns i = some rcn) → rcn.wellFormed
  rcnsFinite :      { i | rtr.rcns i ≠ none }.finite
  nestFiniteRtrs :  { i | rtr.nest i ≠ none }.finite
  wfRoles :         rtr.roles.ids = rtr.ports.ids
  wfNormDeps :      ∀ n i r, rtr.rcns i = some n → n.isNorm → ↑(n.deps r) ⊆ ↑(rtr.ports' r).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' r.opposite).ids}
  wfMutDeps :       ∀ m i, rtr.rcns i = some m → m.isMut → (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (↑(m.deps Role.out) ⊆ ↑(rtr.ports' Role.out).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' Role.in).ids})
  mutsBeforeNorms : ∀ iₙ iₘ n m, rtr.rcns iₙ = some n → n.isNorm → rtr.rcns iₘ = some m → m.isMut → rtr.prios.lt iₘ iₙ
  mutsLinearOrder : ∀ i₁ i₂ m₁ m₂, rtr.rcns i₁ = some m₁ → rtr.rcns i₂ = some m₂ → m₁.isMut → m₂.isMut → (rtr.prios.le i₁ i₂ ∨ rtr.prios.le i₂ i₁) 

-- To define properties of reactors recursively, we need a concept of containment.
-- Containment in a reactor can come in two flavors: 
--
-- 1. `nested`: `r₁` contains `r₂` directly as nested reactor
-- 2. `creatable`: there exists a reaction (which must be a mutation) in `r₁` which
--    can produce a `Raw.Change.create` which contains `r₂`
--
-- The `isAncestorOf` relation forms the transitive closure over the previous cases.
inductive isAncestorOf : (Raw.Reactor ι υ) → (Raw.Reactor ι υ) → Prop 
  | nested {parent child i} : (parent.nest i = some child) → isAncestorOf parent child
  | creatable {old new rcn p s i iᵣ} : (old.rcns i = some rcn) → (Change.create new iᵣ ∈ rcn.body p s) → isAncestorOf old new
  | trans {r₁ r₂ r₃} : (isAncestorOf r₁ r₂) → (isAncestorOf r₂ r₃) → (isAncestorOf r₁ r₃)

-- This property ensures "properness" of a reactor in two steps:
-- 
-- 1. `direct` ensures that the given reactor satisfies all constraints
--    required for a "proper" reactor.
-- 2. `offspring` ensures that all nested and creatable reactors also satisfy `directlyWellFormed`.
--    The `isAncestorOf` relation formalizes the notion of (transitive) nesting and "creatability".
structure wellFormed (σ : Raw.Reactor ι υ) : Prop where
  direct : σ.directlyWellFormed 
  offspring : ∀ {rtr : Raw.Reactor ι υ}, σ.isAncestorOf rtr → rtr.directlyWellFormed

end Raw.Reactor

-- A `Reactor` is a raw reactor that is also well-formed.
--
-- Side note: 
-- The `fromRaw ::` names the constructor of `Reactor`.
structure Reactor (ι υ) [Value υ] where
  fromRaw ::
    raw : Raw.Reactor ι υ
    rawWF : raw.wellFormed  

-- An raw-based extensionality theorem for `Reactor`.
-- We also define a proper extensionality theorem called `ext_iff`.
theorem Reactor.raw_ext_iff {rtr₁ rtr₂ : Reactor ι υ} : rtr₁ = rtr₂ ↔ rtr₁.raw = rtr₂.raw := by
  apply Iff.intro <;> (
    intro h
    cases rtr₁
    cases rtr₂
    simp at h
    simp [h]
  )

theorem Raw.Reactor.isAncestorOf_preserves_wf {rtr₁ rtr₂ : Raw.Reactor ι υ} (ha : rtr₁.isAncestorOf rtr₂) (hw : rtr₁.wellFormed) :
  rtr₂.wellFormed := {
    direct := hw.offspring ha,
    offspring := λ hr => hw.offspring (isAncestorOf.trans ha hr)
  }