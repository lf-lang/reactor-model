import ReactorModel.Components.Reactor.Basic

open Classical Port

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Cmp
  | rtr -- Nested reactors
  | rcn -- Reactions
  | prt -- Port
  | act -- Actions
  | stv -- State variables

namespace Cmp 

-- The *type* corresponding to the component labeled by a given `Cmp`.
-- 
-- Note that the types for `prt` and `stv` are just `υ`, because IDs don't refer to
-- the entire entire mappinngs, but rather the single values within them.
abbrev type : Cmp → Type _
  | rtr => Reactor
  | rcn => Reaction
  | prt => Port
  | act => Time.Tag ▸ Value
  | stv => Value

-- Associates each type of component with the finmap in which it can be found inside
-- of a reactor. We use this in `objFor` to generically resolve the lookup for *some*
-- component and *some* ID.
private abbrev accessor : (cmp : Cmp) → Reactor → ID ▸ cmp.type
  | rtr => Reactor.nest
  | rcn => Reactor.rcns
  | prt => Reactor.ports
  | act => Reactor.acts
  | stv => Reactor.state

end Cmp

namespace Reactor

abbrev cmp (σ : Reactor) (cmp : Cmp) : ID ▸ cmp.type := 
  cmp.accessor σ

namespace Lineage

def target {σ i} : Lineage σ i → Cmp 
  | rtr _ => Cmp.rtr
  | rcn _ => Cmp.rcn
  | prt _ => Cmp.prt
  | act _ => Cmp.act
  | stv _ => Cmp.stv
  | nest l _ => target l

def cmp {σ i} : (cmp : Cmp) → (h : i ∈ (σ.cmp cmp).ids) → Lineage σ i
  | Cmp.rtr, h => Lineage.rtr h
  | Cmp.rcn, h => Lineage.rcn h
  | Cmp.prt, h => Lineage.prt h
  | Cmp.act, h => Lineage.act h
  | Cmp.stv, h => Lineage.stv h

-- The "parent" in a lineage is the reactor which contains the target of the lineage.
-- This function returns that reactor along with its ID.
-- If the direct parent is the top-level reactor `σ`, then the ID is `⊤`.
def parent {σ i} : Lineage σ i → (Rooted ID × Reactor)
  | @nest _ _ r j l _ => 
    match l with 
    | nest .. => parent l
    | _ => (j, r)
  | _ => (⊤, σ)

@[simp] theorem cmp_parent {σ i cmp} (h : i ∈ (σ.cmp cmp).ids) : (Lineage.cmp cmp h).parent.snd = σ := by
  cases Reactor.Lineage.cmp cmp h <;> sorry -- simp [parent]: failed to generate equality theorems for `match` expression

@[simp] theorem nest_parent {σ : Reactor} {rtr i j} (l : Lineage rtr i) (h : σ.nest j = some rtr) : (Lineage.nest l h).parent.snd = l.parent.snd := by
  cases l <;> sorry -- simp [parent]: failed to generate equality theorems for `match` expression

private def retarget {σ i} : (l : Lineage σ i) → (cmp : Cmp) → i ∈ (l.parent.snd.cmp cmp).ids → Lineage σ i
  | nest l' h', cmp, h => Lineage.nest (retarget l' cmp h) h'
  | _, cmp, h => Lineage.cmp cmp h

private theorem retarget_target {σ i} (l : Lineage σ i) (cmp h) :
  (l.retarget cmp h).target = cmp := sorry

private theorem retarget_ne {σ i cmp} (l : Lineage σ i) (h) :
  cmp ≠ l.target → l ≠ l.retarget cmp h := by 
  intro hn hc
  have h' := Lineage.retarget_target l cmp h
  rw [←hc] at h'
  exact absurd h'.symm hn

end Lineage

-- The `Container` relation is used to determine whether a given ID `c`
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
-- we could easily extend the definition of `Container` to check whether `i = ⊤`
-- and yield `False` in that case (as the top-level reactor will never have a
-- parent container).
inductive Container (σ : Reactor) (cmp : Cmp) (i : ID) (c : Rooted ID) : Prop
  | intro (l : Lineage σ i) : (l.parent.fst = c) → (l.target = cmp) → Container σ cmp i c

-- This notation is chosen to be akin to the address notation in C.
notation σ:max " &[" cmp ":" i "]= " c:max => Reactor.Container σ cmp i c

-- In the `Container` relation, any given ID can have at most one parent.
theorem Container.unique {σ : Reactor} {cmp : Cmp} {i : ID} {c₁ c₂ : Rooted ID} :
  (σ &[cmp:i]= c₁) → (σ &[cmp:i]= c₂) → c₁ = c₂ := by
  intro ⟨l₁, h₁, _⟩ ⟨l₂, h₂, _⟩
  simp [←h₁, ←h₂, σ.uniqueIDs l₁ l₂]

def contains (σ : Reactor) (cmp : Cmp) (i : ID) : Prop :=
  ∃ c, σ &[cmp:i]= c

-- NOTE: As we have `Container.unique`, the choice of object is always unique.
noncomputable def container? (σ : Reactor) (cmp : Cmp) (i : ID) : Option (Rooted ID) := 
  if h : ∃ c, σ &[cmp:i]= c then h.choose else none

-- The `Object` relation is used to determine whether a given ID `i` identifies
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
inductive Object (σ : Reactor) : Rooted ID → (cmp : Cmp) → cmp.type → Prop
  | root {o} : (o = σ) → Object σ ⊤ Cmp.rtr o
  | nest {i cmp o} (l : Lineage σ i) : (l.parent.snd.cmp cmp i = some o) → Object σ (Rooted.nest i) cmp o 
  
-- This notation is chosen to be akin to the dereference notation in C.
notation σ:max " *[" cmp ":" i "]= " o:max => Reactor.Object σ i cmp o

-- In the `Object` relation, any given ID can have associated objects of at most one component type.
-- E.g. an ID cannot have associated objects of type `Cmp.rcn` *and* `Cmp.prt`.
-- Cf. `objFor_unique_obj` for further information.
theorem Object.unique_cmp {σ : Reactor} {i : Rooted ID} {cmp₁ cmp₂ : Cmp} {o₁ : cmp₁.type} {o₂ : cmp₂.type} :
  (σ *[cmp₁:i]= o₁) → (σ *[cmp₂:i]= o₂) → cmp₁ = cmp₂ := by
  intro h₁ h₂
  cases h₁ <;> cases h₂ <;> simp only
  case nest.nest l₁ h₁ l₂ h₂ =>
    have hu := σ.uniqueIDs l₁ l₂
    rw [←hu] at h₂
    by_contra hc
    have h₁ := Finmap.ids_def'.mpr ⟨_, h₁.symm⟩
    have h₂ := Finmap.ids_def'.mpr ⟨_, h₂.symm⟩
    by_cases hc₁ : cmp₁ = l₁.target
    case neg => exact absurd (σ.uniqueIDs l₁ $ l₁.retarget cmp₁ h₁) (Lineage.retarget_ne l₁ h₁ hc₁)
    case pos =>
      by_cases hc₂ : cmp₂ = l₂.target
      case neg => exact absurd (σ.uniqueIDs l₂ $ l₂.retarget cmp₂ h₂) (Lineage.retarget_ne l₂ h₂ hc₂)
      case pos =>
        rw [hu] at hc₁
        rw [←hc₂] at hc₁
        contradiction

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
-- object equality. X
theorem Object.unique_obj {σ : Reactor} {i : Rooted ID} {cmp : Cmp} {o₁ o₂ : cmp.type} : 
  (σ *[cmp:i]= o₁) → (σ *[cmp:i]= o₂) → o₁ = o₂ := by
  intro h₁ h₂
  cases h₁ <;> cases h₂
  case root.root h₁ h₂ => exact h₁.trans h₂.symm
  case nest.nest l₁ h₁ l₂ h₂ => 
    rw [σ.uniqueIDs l₁ l₂] at h₁
    exact Option.some_inj.mp $ h₁.symm.trans h₂

-- NOTE: As we have `Object.unique_obj`, the choice of object is always unique.
noncomputable def obj? (σ : Reactor) (cmp : Cmp) : (Rooted ID) ▸ cmp.type := {
  lookup := λ i => if h : ∃ o, σ *[cmp:i]= o then h.choose else none,
  finite := sorry
}

noncomputable def containerObj? (σ : Reactor) (cmp : Cmp) (i : ID) : Option Reactor :=
  σ.container? cmp i >>= (σ.obj? .rtr ·)

noncomputable def ids (σ : Reactor) (cmp : Cmp) : Finset ID :=
  let description := { i : ID | σ.contains cmp i }
  let finite : description.finite := sorry
  finite.toFinset

theorem ids_def {σ : Reactor} {cmp : Cmp} {i : ID} : 
  (σ.contains cmp i) ↔ i ∈ σ.ids cmp := by
  constructor <;> (
    intro h
    simp only [ids, Set.finite.mem_to_finset] at *
    exact h
  )

noncomputable def allIDs (σ : Reactor) : Finset ID :=
  let description := { i : ID | ∃ cmp, i ∈ σ.ids cmp }
  let finite : description.finite := sorry
  finite.toFinset

theorem Object.ext {σ₁ σ₂ : Reactor} (hi : σ₁.allIDs = σ₂.allIDs) (hv : ∀ cmp i v, σ₁ *[cmp:i]= v → σ₂ *[cmp:i]= v) : 
  σ₁ = σ₂ := by
    sorry

end Reactor