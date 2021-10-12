import ReactorModel.Mathlib

open Classical

-- A partial map defined for only finitely many inputs.
-- This is akin to what is sometimes called a hashmap/dictionary/associative array.
structure Finmap (α β) where
  lookup : α → Option β 
  finite : { a | lookup a ≠ none }.finite

namespace Finmap

infix:50 " ▸ " => (λ a b => Finmap a b)

-- A coercion so that finmaps can be called directly as functions.
instance : CoeFun (α ▸ β) (λ _ => α → Option β) where
  coe f := f.lookup

instance : EmptyCollection (α ▸ β) where
  emptyCollection := {lookup := (λ _ => none), finite := @Set.finite_empty α}  

instance : Inhabited (Finmap α β) where
  default := ∅

-- The (finite) set of inputs for which a given finmap has an associated value.
noncomputable def ids (f : α ▸ β) : Finset α :=
  let description := { i | f i ≠ none }
  let finite : description.finite := f.finite
  finite.toFinset

theorem idsDef {f : α ▸ β} {i : α} : i ∈ f.ids ↔ f i ≠ none := by
  simp [ids, Set.finite.mem_to_finset, Set.mem_set_of_eq]

-- The (finite) set of values for which there exist inputs that map to them.
noncomputable def values (f : α ▸ β) : Finset β :=
  let description := { v | ∃ i, f i = v }
  let finite : description.finite := by
    let s := f.ids.image f.lookup
    let t := { v | ∃ i, f i = some v }.image Option.some
    suffices h : t ⊆ ↑s from Set.finite.subset (Finset.finite_to_set s) h
    intro x h
    simp at *
    obtain ⟨b, ⟨a, ha⟩, hb⟩ := h
    exists a
    rw [idsDef]
    split
    simp [ha]
    simp [ha, hb]
  finite.toFinset

theorem valuesDef {f : α ▸ β} {v : β} : v ∈ f.values ↔ (∃ i, f i = some v) := by
  simp [values, Set.finite.mem_to_finset, Set.mem_set_of_eq]

-- The (finite) set of identifier-value pairs which define the finmap.
noncomputable def entries (f : α ▸ β) : Finset (α × β) :=
  let description := { e | f e.fst = e.snd }
  let finite : description.finite := sorry
  finite.toFinset

noncomputable def update (f : α ▸ β) (a : α) (b : Option β) : α ▸ β := {
  lookup := Function.update f.lookup a b,
  finite := sorry
}

-- Sometimes when using `update`, the parameter `b` isn't lifted to be an `Option` automatically.
-- In this case `update'` can be used.
noncomputable def update' (f : α ▸ β) (a : α) (b : β) : α ▸ β := f.update a b

-- The finmap that combines a given finmap `f` with a function `g`
-- by mapping all (defined) values in `f` through `g`. 
def map (f : α ▸ β) (g : β → γ) : Finmap α γ := {
  lookup := λ i => (f i) >>= (some ∘ g),
  finite := by
    suffices h : { a | (λ i => (f i) >>= (some ∘ g)) a ≠ none } ⊆ ↑f.ids
      from Set.finite.subset (Finset.finite_to_set _) h
    simp
    intro x h
    obtain ⟨_, ⟨_, ⟨hb, _⟩⟩⟩ := h
    simp [idsDef, Option.ne_none_iff_exists, hb]
}

noncomputable def filter (f : α ▸ β) (p : α → Prop) : Finmap α β := {
  lookup := λ i => if p i then f i else none,
  finite := sorry
}

noncomputable def filter' (f : α ▸ β) (p : β → Prop) : Finmap α β := {
  lookup := (λ i => 
    match f i with
    | some b => if p b then b else none
    | none => none
  ),
  finite := sorry
}

end Finmap