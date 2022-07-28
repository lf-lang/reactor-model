import ReactorModel.Mathlib.Set
import ReactorModel.Mathlib.Tactics
import ReactorModel.Mathlib.Option

open Classical

-- NOTE: 
-- Despite this file not matching Mathlib's definition of a finmap,
-- we might still want to use Mathlib's version once it is ported.
-- Hence, there it is not necessary to resolve the sorrys in this file (yet).

-- A partial map defined for only finitely many inputs.
-- This is akin to what is sometimes called a hashmap/dictionary/associative array.
structure Finmap (α β) where
  lookup : α → Option β 
  finite : { a | lookup a ≠ none }.finite

namespace Finmap

infixr:50 " ⇉ " => (λ a b => Finmap a b)

-- A coercion so that finmaps can be called directly as functions.
instance : CoeFun (α ⇉ β) (λ _ => α → Option β) where
  coe f := f.lookup

-- This allows us to use `∅` as notation for the empty finite map.
instance : EmptyCollection (α ⇉ β) where 
  emptyCollection := {lookup := (λ _ => none), finite := @Set.finite_empty α}  

instance : Inhabited (Finmap α β) where
  default := ∅

@[simp]
theorem empty_lookup_none : (∅ : α ⇉ β).lookup i = none := by 
  rfl

theorem ext_iff {f₁ f₂ : α ⇉ β} : f₁ = f₂ ↔ ∀ i, f₁ i = f₂ i :=
  sorry

@[ext]
theorem ext (f₁ f₂ : α ⇉ β) (h : ∀ i, f₁ i = f₂ i) : f₁ = f₂ :=
  ext_iff.mpr h

-- The (finite) set of inputs for which a given finmap has an associated value.
noncomputable def ids (f : α ⇉ β) : Finset α :=
  let description := { i | f i ≠ none }
  let finite : description.finite := f.finite
  finite.toFinset

theorem ids_def {f : α ⇉ β} {i : α} : i ∈ f.ids ↔ f i ≠ none := by
  simp [ids, Set.finite.mem_to_finset, Set.mem_set_of_eq]

theorem ids_def' {f : α ⇉ β} {i : α} : i ∈ f.ids ↔ ∃ b, f i = some b := by
  apply Iff.intro
  case mp =>  exact λ h => ⟨_, (Option.ne_none_iff_exists.mp $ ids_def.mp h).choose_spec.symm⟩
  case mpr => exact λ ⟨_, h⟩ => ids_def.mpr $ Option.ne_none_iff_exists.mpr ⟨_, h.symm⟩

@[simp]
theorem empty_ids_empty : (∅ : α ⇉ β).ids = ∅ := by 
  apply Finset.ext
  simp [ids_def]

def nonempty (f : α ⇉ β) : Prop := ∃ i, f i ≠ none

noncomputable def lookup' (f : α ⇉ β) {i : α} (h : i ∈ f.ids) : β :=
   Exists.choose $ ids_def'.mp h
   
-- The (finite) set of values for which there exist inputs that map to them.
noncomputable def values (f : α ⇉ β) : Finset β :=
  let description := { v : β | ∃ i, f i = v }
  let finite : description.finite := by
    let s := f.ids.image f.lookup
    let t := { v | ∃ i, f i = some v }.image Option.some
    suffices h : t ⊆ ↑s from Set.finite.subset (Finset.finite_to_set s) h
    intro x h
    simp at *
    have ⟨b, ⟨a, ha⟩, hb⟩ := h
    exists a
    apply And.intro
    case left => simp [ids_def, ha]
    case right => simp [ha, hb]
  finite.toFinset

theorem values_def {f : α ⇉ β} {v : β} : v ∈ f.values ↔ (∃ i, f i = some v) := by
  simp [values, Set.finite.mem_to_finset, Set.mem_set_of_eq]

-- The (finite) set of identifier-value pairs which define the finmap.
noncomputable def entries (f : α ⇉ β) : Finset (α × β) :=
  let description := { e | f e.fst = e.snd }
  let finite : description.finite := sorry
  finite.toFinset

-- Replaces a single indentifier-value pair in a given finmap with a given new value.
-- This can also be used to remove the value for an identifier by passing a value of `none`,
-- as well as adding a new entry to the finmap, if the given identifier is not yet part of
-- the finmap.
noncomputable def update (f : α ⇉ β) (a : α) (b : Option β) : α ⇉ β := {
  lookup := Function.update f.lookup a b,
  finite := sorry
}

-- Sometimes when using `update`, the parameter `b` isn't lifted to be
-- an `Option` automatically. In this case `update'` can be used.
noncomputable def update' (f : α ⇉ β) (a : α) (b : β) : α ⇉ β := f.update a b

theorem update_nonempty (f : α ⇉ β) (a : α) (b : β) : f.nonempty → (f.update a b).nonempty := sorry

theorem update_self (f : α ⇉ β) {a : α} (b : Option β) : (f.update a b) a = b :=
  sorry

theorem update_ne (f : α ⇉ β) {a a' : α} (h : a ≠ a') (b : Option β) : (f.update a b) a' = f a' :=
  sorry

-- The finmap that combines a given finmap `f` with a function `g`
-- by mapping all (defined) values in `f` through `g`. 
def map (f : α ⇉ β) (g : β → γ) : α ⇉ γ := {
  lookup := λ a => (f a) >>= (some ∘ g),
  finite := by
    suffices h : { a | (λ i => (f i) >>= (some ∘ g)) a ≠ none } ⊆ ↑f.ids
      from Set.finite.subset (Finset.finite_to_set _) h
    intro x h
    simp only [ids_def]
    sorry
}

theorem map_mem_ids {f : α ⇉ β} {g : β → γ} {i} : i ∈ (f.map g).ids ↔ i ∈ f.ids :=
  sorry

theorem map_def {f : α ⇉ β} {g : β → γ} {i v} (h : (f.map g) i = some v) : ∃ m, f i = some m ∧ g m = v :=
  sorry

noncomputable def map' (f : α ⇉ γ) (g : α → Option β) (h : g.injective) : β ⇉ γ := {
  lookup := λ b => 
    if h : ∃ a ∈ f.ids, g a = b -- This is unique because of h.
    then f h.choose
    else none
  finite := sorry
}

theorem map'_def {f : α ⇉ γ} : (g a = some b) → (f.map' g h b = f a) :=
  sorry   

def attach (f : α ⇉ β) : α ⇉ { b // b ∈ f.values } := {
  lookup := λ a =>
    match h:(f a) with
    | none => none
    | some b => some ⟨b, (values_def.mpr ⟨a, h⟩)⟩,
  finite := sorry
}

theorem attach_mem_ids {f : α ⇉ β} {i} : i ∈ f.attach.ids ↔ i ∈ f.ids :=
  sorry

theorem attach_def {f : α ⇉ β} {i} {b : β} {hb} (h : f.attach i = some ⟨b, hb⟩) : f i = b :=
  sorry

-- The finmap that contains only those entries from `f`, whose identifiers
-- satisfy the given predicate `p`.
noncomputable def filter (f : α ⇉ β) (p : α → Prop) : α ⇉ β := {
  lookup := λ a => if p a then f a else none,
  finite := sorry
}

-- The finmap that contains only those entries from `f`, whose values
-- satisfy the given predicate `p`.
noncomputable def filter' (f : α ⇉ β) (p : β → Prop) : α ⇉ β := {
  lookup := (λ a => 
    match f a with
    | some b => if p b then b else none
    | none => none
  ),
  finite := sorry
}

theorem filter'_mem {f : α ⇉ β} {p : β → Prop} {i : α} {b : β} : 
  (f.filter' p) i = some b ↔ f i = b ∧ p b :=
  sorry

theorem filter'_mem_values {f : α ⇉ β} {p : β → Prop} {b : β} : 
  b ∈ (f.filter' p).values ↔ ∃ i : α, f i = b ∧ p b :=
  sorry 

def filterMap (f : α ⇉ β) (g : β → Option γ) : α ⇉ γ := {
  lookup := λ a => (f a) >>= g,
  finite := sorry
}

theorem filterMap_congr {f₁ f₂ : α ⇉ β} : (f₁ a = f₂ a) → (f₁.filterMap g a = f₂.filterMap g a) :=
  sorry

-- The finmap that containts only those entries from `f`, whose identifiers
-- are in a given set `as`.
noncomputable def restrict (f : α ⇉ β) (as : Finset α) : α ⇉ β :=
  f.filter (λ a => a ∈ as)

theorem restrict_ext {f₁ f₂ : α ⇉ β} {as : Finset α} : 
  (∀ a ∈ as, f₁ a = f₂ a) → f₁.restrict as = f₂.restrict as := 
  sorry

-- This relation is true if two given finmaps are defined on the same IDs,
-- and each pair of values for a given ID fulfills a relation `r`.
--
-- Note, the name `forall₂` is chosen to match the analogous relation on `List`.
structure forall₂ (r : β → γ → Prop) (f₁ : α ⇉ β) (f₂ : α ⇉ γ) : Prop where
  eqIDs : f₁.ids = f₂.ids
  rel : ∀ a (b : β) (c : γ), (f₁ a = b) → (f₂ a = c) → r b c

structure forall₂' (r : β → γ → Prop) (f₁ : α ⇉ β) (f₂ : α → Option γ) : Prop where
  eqIDs : ∀ a, a ∈ f₁.ids ↔ f₂ a ≠ none
  rel : ∀ {a} {b : β} {c : γ}, (f₁ a = b) → (f₂ a = c) → r b c

def union (f₁ f₂ : α ⇉ β) : α ⇉ β := {
  lookup := λ a => (f₁ a).elim (f₂ a) .some,
  finite := sorry
}

instance : Union (α ⇉ β) := ⟨union⟩

end Finmap