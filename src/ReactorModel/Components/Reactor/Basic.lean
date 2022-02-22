import ReactorModel.Components.Raw

open Port

-- Cf. `Reactor.Lineage`.
inductive Raw.Reactor.Lineage : Raw.Reactor → ID → Type _ 
  | rtr σ i : σ.nest i ≠ none → Lineage σ i
  | rcn σ i : σ.rcns i ≠ none → Lineage σ i
  | prt σ i : i ∈ σ.ports.ids → Lineage σ i
  | act σ i : i ∈ σ.acts.ids  → Lineage σ i
  | stv σ i : i ∈ σ.state.ids → Lineage σ i
  | nest {σ σ' i i'} : (Lineage σ' i) → (σ.nest i' = some σ') → Lineage σ i

-- These are the constraints required for a "proper" reaction.
-- They are used in `Reaction.fromRaw` to lift a `Raw.Reaction` to a
-- "proper" `Reaction`.
structure Raw.Reaction.wellFormed (rcn : Raw.Reaction) : Prop where
  tsSubInDeps :   rcn.triggers ⊆ rcn.deps Role.in                                     
  prtOutDepOnly : ∀ i {o} (v : Value), (o ∉ rcn.deps Role.out) → Raw.Change.port o v ∉ rcn.body i
  actOutDepOnly : ∀ i {o} t (v : Value), (o ∉ rcn.deps Role.out) → (Raw.Change.action o t v) ∉ rcn.body i
  actNotPast :    ∀ i a t (v : Value), (Raw.Change.action a t v) ∈ rcn.body i → i.time.t ≤ t

inductive Raw.Reactor.rcnsNeedTotalOrder (rtr : Raw.Reactor) (rcn₁ rcn₂ : Raw.Reaction) 
  | impure {i₁ i₂} : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (¬rcn₁.isPure) → (¬rcn₂.isPure) → rcnsNeedTotalOrder rtr rcn₁ rcn₂
  | output {i₁ i₂} : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.deps Role.out ∩ rcn₂.deps Role.out ≠ ∅) → rcnsNeedTotalOrder rtr rcn₁ rcn₂
  | muts   {i₁ i₂} : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.isMut) → (rcn₂.isMut) → rcnsNeedTotalOrder rtr rcn₁ rcn₂

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
structure directlyWellFormed (rtr : Raw.Reactor) : Prop where
  uniqueIDs :       ∀ l₁ l₂ : Lineage rtr i, l₁ = l₂ 
  rcnsWF :          ∀ {rcn}, (∃ i, rtr.rcns i = some rcn) → rcn.wellFormed
  rcnsFinite :      { i | rtr.rcns i ≠ none }.finite
  nestFiniteRtrs :  { i | rtr.nest i ≠ none }.finite
  uniqueInputCons : ∀ {iₚ p iₙ n i₁ rcn₁ i₂ rcn₂}, rtr.nest iₙ = some n → n.ports iₚ = some p → p.role = Role.in → rtr.rcns i₁ = some rcn₁ → rtr.rcns i₂ = some rcn₂ → i₁ ≠ i₂ → iₚ ∈ rcn₁.deps Role.out → iₚ ∉ rcn₂.deps Role.out
  wfNormDeps :      ∀ n i r, rtr.rcns i = some n → n.isNorm → ↑(n.deps r) ⊆ ↑rtr.acts.ids ∪ ↑(rtr.portVals r).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.portVals r.opposite).ids}
  wfMutDeps :       ∀ m i, rtr.rcns i = some m → m.isMut → (m.deps Role.in ⊆ (rtr.portVals Role.in).ids) ∧ (↑(m.deps Role.out) ⊆ ↑(rtr.portVals Role.out).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.portVals Role.in).ids})
  rcnsTotalOrder :  ∀ {rcn₁ rcn₂}, rtr.rcnsNeedTotalOrder rcn₁ rcn₂ → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio) 

-- To define properties of reactors recursively, we need a concept of containment.
-- Containment in a reactor can come in two flavors: 
--
-- 1. `nested`: `r₁` contains `r₂` directly as nested reactor
-- 2. `creatable`: there exists a reaction (which must be a mutation) in `r₁` which
--    can produce a `Raw.Change.create` which contains `r₂`
--
-- The `Ancestor` relation forms the transitive closure over the previous cases.
inductive Ancestor : Raw.Reactor → Raw.Reactor → Prop 
  | nested {parent child i} : (parent.nest i = some child) → Ancestor parent child
  | creatable {old new rcn inp i} : (old.rcns i = some rcn) → (Change.create new ∈ rcn.body inp) → Ancestor old new
  | trans {r₁ r₂ r₃} : (Ancestor r₁ r₂) → (Ancestor r₂ r₃) → (Ancestor r₁ r₃)

-- This property ensures "properness" of a reactor in two steps:
-- 
-- 1. `direct` ensures that the given reactor satisfies all constraints
--    required for a "proper" reactor.
-- 2. `offspring` ensures that all nested and creatable reactors also satisfy `directlyWellFormed`.
--    The `isAncestorOf` relation formalizes the notion of (transitive) nesting and "creatability".
structure wellFormed (σ : Raw.Reactor) : Prop where
  direct : σ.directlyWellFormed 
  offspring : ∀ {rtr : Raw.Reactor}, Ancestor σ rtr → rtr.directlyWellFormed

end Raw.Reactor

-- A `Reactor` is a raw reactor that is also well-formed.
--
-- Side note: 
-- The `fromRaw ::` names the constructor of `Reactor`.
structure Reactor where
  fromRaw ::
    raw : Raw.Reactor
    rawWF : raw.wellFormed  

-- An raw-based extensionality theorem for `Reactor`.
-- We also define a proper extensionality theorem called `ext_iff`.
theorem Reactor.raw_ext_iff {rtr₁ rtr₂ : Reactor} : rtr₁ = rtr₂ ↔ rtr₁.raw = rtr₂.raw := by
  constructor <;> (
    intro h
    cases rtr₁
    cases rtr₂
    simp at h
    simp [h]
  )

theorem Raw.Reactor.Ancestor.preserves_wf {rtr₁ rtr₂ : Raw.Reactor} (ha : Ancestor rtr₁ rtr₂) (hw : rtr₁.wellFormed) :
  rtr₂.wellFormed := {
    direct := hw.offspring ha,
    offspring := λ hr => hw.offspring (Ancestor.trans ha hr)
  }