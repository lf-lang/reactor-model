import ReactorModel.Components.Reactor.Properties

open Classical 

-- TODO: Redoc
-- TODO: Better notation for cmp.accessor σ, e.g. σ[cmp]

-- Note that `ι` and `υ` live in the same universe:
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Stuck.20at.20solving.20universe.20constraint/near/253232009
variable (ι υ : Type u) [Value υ]

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Cmp
  | rtr -- Nested reactors
  | rcn -- Reactions
  | prt -- Ports
  | stv -- State variables

namespace Cmp 

-- The *type* corresponding to the component labeled by a given `Cmp`.
-- 
-- Note that the types for `prt` and `stv` are just `υ`, because IDs don't refer to
-- entire instances of `Ports` or `StateVars`, but rather the single values within them.
abbrev type : Cmp → Type _
  | rtr => Reactor ι υ
  | rcn => Reaction ι υ
  | prt => υ
  | stv => υ

variable {ι υ}

-- Associates each type of component with the finmap in which it can be found inside
-- of a reactor. We use this in `objFor` to generically resolve the lookup for *some*
-- component and *some* ID.
def accessor : (cmp : Cmp) → Reactor ι υ → (ι ▸ cmp.type ι υ)
  | rtr => Reactor.nest
  | rcn => Reactor.rcns
  | prt => Reactor.ports
  | stv => Reactor.state

end Cmp

variable {ι υ}

namespace Reactor

-- TODO: Docs
--       Mention that we do the whole Option ι so that ⊤ can never appear inside a reactor.
--       Its more like a label.
notation "⊤" => none

-- The "direct parent" in a lineage is the reactor which contains the target of the lineage.
-- This function returns that reactor along with its ID.
-- If the direct parent is the top-level reactor `σ`, then the ID is `⊤`.
def Lineage.directParent {σ : Reactor ι υ} {i} : Lineage σ i → (Option ι × Reactor ι υ)
  | rtr _ => (⊤, σ)
  | rcn _ => (⊤, σ)
  | prt _ => (⊤, σ)
  | stv _ => (⊤, σ)
  | nest σ' i' (rtr _) _ => (i', σ')
  | nest σ' i' (rcn _) _ => (i', σ')
  | nest σ' i' (prt _) _ => (i', σ')
  | nest σ' i' (stv _) _ => (i', σ')
  | nest _  _  l       _ => directParent l -- By case distinction `l` is a `Lineage.nest`.

-- The `containerOf` relation is used to determine whether a given ID `c`
-- identifies a reactor that contains a given object identified by ID `i`.
-- In other words, whether `c` identifies the parent of `i`.
-- The *kind* of component addressed by `i` is not required, as all IDs in
-- a reactor are unique (by `Reactor.uniqueIDs`).
--
-- Formalization:
-- We use the concept of lineages to "find" the path of reactor-IDs that leads
-- us through `σ` to `i`. If such a lineage exists we check whether `c` is the ID
-- of the last reactor in that path, because by construction (of lineages) *that* 
-- is the reactor that contains `i`.
-- Note that while `c` *can* be the top-level ID `⊤`, `i` can't.
-- We need to restrict `i` in this way, because `Lineage`s are only defined over
-- non-optional IDs. In practice, this isn't really a restriction though, because
-- we could easily extend the definition of `containerOf` to check whether `i = ⊤`
-- and yield `False` in that case (as the top-level reactor will never have a
-- parent container).
def containerOf (σ : Reactor ι υ) (i : ι) (c : Option ι) : Prop := 
  ∃ l : Lineage σ i, (l.directParent).fst = c 

-- This notation is chosen to be akin to the address notation in C.
notation σ:max " &[" i "]= " c:max => Reactor.containerOf σ i c

-- In the `containerOf` relation, any given ID can have at most one parent (`containerOf` is functional).
theorem containerOf_unique {σ : Reactor ι υ} {i : ι} {c₁ c₂ : Option ι} :
  σ &[i]= c₁ → σ &[i]= c₂ → c₁ = c₂ := by
  intro h₁ h₂
  obtain ⟨l₁, h₁⟩ := h₁
  obtain ⟨l₂, h₂⟩ := h₂
  simp [←h₁, ←h₂, σ.uniqueIDs l₁ l₂]

-- The `objFor` relation is used to determine whether a given ID `i` identifies
-- an object `o` of component type `cmp`.
--
-- Example: 
-- If `σ.objFor Cmp.rcn i x`, then:
-- * `σ` is the "context" (top-level) reactor.
-- * `i` is interpreted as being an ID that refers to a reaction (because of `Cmp.rcn`).
-- * `x` is the `Reaction` identified by `i`.
--
-- Formalization:
-- We use the concept of lineages to "find" the path of reactor-IDs that leads
-- us through `σ` to `i`. If such a lineage exists we obtain the last reactor in
-- that path (`l.directParent.snd`). From that reactor we try to obtain an object 
-- identified by `i` of component kind `cmp` (cf. `Cmp.accessor`).
-- We then check whether the given object `o` matches that object.
--
-- Technicalities:
-- The left side of the equality produces an optional value, as it is possible
-- that no value of component kind `cmp` is found for ID `i`.
-- Thus the right side is automatically lifted by Lean to `some o`. 
-- It *would* be possible to avoid this optionality, as a lineage for `i` always
-- contains a proof that `i` identifies an object in its parent reactor.
-- In this case the kind of lineage and given `cmp` would have to be matched, e.g. 
-- by adding an instance of `Cmp` into the type of `Lineage`.
-- This leads to heterogeneous equality though, and is therefore undesirable:
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20Exfalso.20HEq
def objFor (σ : Reactor ι υ) (cmp : Cmp) (i : ι) (o : cmp.type ι υ) : Prop := 
  ∃ l : Lineage σ i, (cmp.accessor l.directParent.snd) i = o

-- This notation is chosen to be akin to the dereference notation in C.
notation σ:max " *[" cmp ", " i "]= " o:max => Reactor.objFor σ cmp i o

-- In the `objFor` relation, any given ID can have associated objects of at most one component type.
-- E.g. an ID cannot have associated objects of type `Cmp.rcn` *and* `Cmp.prt`.
-- Cf. `objFor_unique_obj` for further information.
theorem objFor_unique_cmp {σ : Reactor ι υ} {i : ι} {cmp₁ cmp₂ : Cmp} {o₁ : cmp₁.type ι υ} {o₂ : cmp₂.type ι υ} :
  (σ *[cmp₁, i]= o₁) → (σ *[cmp₂, i]= o₂) → cmp₁ = cmp₂ := by
  sorry

-- In the `objFor` relation, any given ID can have at most one associated object. 
--
-- Technicalities:
-- There are really two aspects of uniqueness that come together in `objFor`.
--
-- 1. Any given ID can have associated objects of at most one component type, as shown by `objFor_unique_cmp`.
-- 2. Any given ID can have a most one associated object of each component type, as shown here.
--
-- The result is that each ID can have at most one associated object, even across component types.
-- We do not show this together as this would involve using `HEq`.
-- If this is important though, the two theorems can be used in succession:
-- First, `objFor_unique_obj` can be used to establish equality of the component types.
-- After appropriate type casting (using the previous result), `objFor_unique_obj` can be used to show
-- object equality. 
theorem objFor_unique_obj {σ : Reactor ι υ} {i : ι} {cmp : Cmp} {o₁ o₂ : cmp.type ι υ} : 
  (σ *[cmp, i]= o₁) → (σ *[cmp, i]= o₂) → o₁ = o₂ := by
  intro h₁ h₂
  obtain ⟨l₁, h₁⟩ := h₁
  obtain ⟨l₂, h₂⟩ := h₂
  have hu := σ.uniqueIDs l₁ l₂
  rw [hu] at h₁
  simp [h₁] at h₂
  exact h₂

-- TODO: Is this theorem true? And do we even need it now that `update` has been redefined?
theorem objFor_ext {σ₁ σ₂ : Reactor ι υ} (cmp : Cmp) (h : ∀ i o, (σ₁ *[cmp, i]= o) ↔ (σ₂ *[cmp, i]= o)) :
  cmp.accessor σ₁ = cmp.accessor σ₂ := by
  ext
  intro i
  have h := h i
  cases h₁ : cmp.accessor σ₁ i <;> cases h₂ : cmp.accessor σ₂ i
  case h.none.none => simp
  case h.none.some o =>
    exfalso
    have h := (h o).mp
    simp only [objFor] at h
    cases cmp
    case h.rtr =>
      have H : ∃ l : Lineage σ₁ i, (Cmp.rtr.accessor (l.directParent).snd) i = some o := sorry
      obtain ⟨l, hl⟩ := h H
      sorry
    sorry
    sorry
    sorry
  case h.some.none o =>
    sorry
  case h.some.some o₁ o₂ =>
    have h₁ := h o₁
    have h₂ := h o₂
    byCases h : σ₁ *[cmp, i]= o₁ <;> byCases h' : σ₁ *[cmp, i]= o₂
    <;> sorry
    -- have H := objFor_unique_obj h₁.mp h₂.mp -- (σ *[cmp, i]= o₁) → (σ *[cmp, i]= o₂) → o₁ = o₂

-- TODO: Does this somehow allow ID-renaming or other reshuffling of data?
inductive update (cmp : Cmp) (v : cmp.type ι υ) : ι → Reactor ι υ → Reactor ι υ → Prop :=
  | top {i σ₁ σ₂} : 
    (∀ cmp' i', (cmp' ≠ cmp ∨ i' ≠ i) → cmp'.accessor σ₁ i' = cmp'.accessor σ₂ i') → 
    (σ₁.prios = σ₂.prios) → 
    (σ₁.roles = σ₂.roles) → 
    (cmp.accessor σ₂ i = v) → 
    update cmp v i σ₁ σ₂
  | nested {i} {σ₁ σ₂} {j} {rtr₁ rtr₂} :
    (∀ cmp', cmp' ≠ Cmp.rtr → cmp'.accessor σ₁ = cmp'.accessor σ₂) → 
    (σ₁.prios = σ₂.prios) → 
    (σ₁.roles = σ₂.roles) → 
    (σ₁.nest j = some rtr₁) →
    (σ₂.nest j = some rtr₂) →
    (∀ j', j' ≠ j → σ₁.nest j' = σ₂.nest j') →
    (update cmp v i rtr₁ rtr₂) →
    update cmp v i σ₁ σ₂

notation σ₁:max " -[" cmp ", " i ":=" v "]→ " σ₂:max => Reactor.update cmp v i σ₁ σ₂

-- The `update` relation is functional.
theorem update_unique {σ σ₁ σ₂  : Reactor ι υ} {cmp : Cmp} {i : ι} {v : cmp.type ι υ} :
  (σ -[cmp, i:=v]→ σ₁) → (σ -[cmp, i:=v]→ σ₂) → σ₁ = σ₂ := by
  intro h₁ h₂
  induction h₁
  case top i σ σ₁ hc hp hr ht =>
    cases h₂
    case top σ' i' ht' hp' hr' hc' =>
      ext
      simp [←hp, hp', ←hr, hr']
      refine ⟨?ports, ?state, ?reactions, ?reactors⟩
      case ports =>
        have HC := hc Cmp.prt i'
        -- Basically the same as commented proof below (for all Cmp kinds).
        sorry
      all_goals { sorry }
    case nested i' j rtr₁ rtr₂ hu hr₁ hr₂ hc' hp' hr' hne =>
      exfalso
      sorry
      -- If we update i at the top level for σ₁ and at a nested
      -- level at σ₂, then σ₁ and σ₂ have i appearing at different
      -- levels. Since IDs are unique, one of the updates can't
      -- actually have happened, as σ can only have i at either the
      -- top level or a nested level, but not both.
  case nested =>
    sorry

  /-intro h₁ h₂
  ext
  simp [←h₁.eqPrios, h₂.eqPrios, ←h₁.eqRoles, h₂.eqRoles]
  refine ⟨?ports, ?state, ?reactions, ?reactors⟩
  case ports =>     exact aux Cmp.prt h₁ h₂
  case state =>     exact aux Cmp.stv h₁ h₂
  case reactions => exact aux Cmp.rcn h₁ h₂
  case reactors =>  exact aux Cmp.rtr h₁ h₂
where 
  aux {σ σ₁ σ₂  : Reactor ι υ} {cmp : Cmp} {i : ι} {v : cmp.type ι υ}  (cmp' : Cmp) (h₁ : σ -[cmp, i := v]→ σ₁) (h₂ : σ -[cmp, i := v]→ σ₂) : 
  cmp'.accessor σ₁ = cmp'.accessor σ₂ := by
  obtain ⟨hc₁, hi₁, _, _, ht₁⟩ := h₁
  obtain ⟨hc₂, hi₂, _, _, ht₂⟩ := h₂
  apply objFor_ext cmp'
  intro j o
  byCases h : cmp' = cmp
  case inl =>
    subst h
    byCases h' : j = i
    case inl =>
      simp [←h'] at ht₁ ht₂
      byCases h'' : o = v
      case inl => simp [h'', iff_of_true ht₁ ht₂]
      case inr =>
        exact Iff.intro
          (λ h => False.elim $ (not_and_self_iff _).mp ⟨h'', objFor_unique_obj h ht₁⟩)
          (λ h => False.elim $ (not_and_self_iff _).mp ⟨h'', objFor_unique_obj h ht₂⟩)
    case inr => simp [←(hi₁ j h'), hi₂ j h']
  case inr => simp [←(hc₁ cmp' h), hc₂ cmp' h]-/

end Reactor
