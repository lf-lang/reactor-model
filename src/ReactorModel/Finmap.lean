import ReactorModel.Mathlib.Set
import ReactorModel.Mathlib.Option

open Classical

structure Finmap (α β) where
  lookup : α → Option β 
  finite : { i | lookup i ≠ none }.finite

namespace Finmap

infix:50 " ▸ " => (λ a b => Finmap a b)

instance : CoeFun (α ▸ β) (λ _ => α → Option β) where
  coe f := f.lookup

instance : EmptyCollection (α ▸ β) where
  emptyCollection := {lookup := (λ _ => none), finite := @Set.finite_empty α}  

instance : Inhabited (Finmap α β) where
  default := ∅

noncomputable def ids (f : α ▸ β) : Finset α :=
  let description := { i | f i ≠ none }
  let finite : description.finite := f.finite
  finite.toFinset

theorem idsDef {f : α ▸ β} {i : α} : i ∈ f.ids ↔ f i ≠ none := by
  simp [ids, Set.finite.mem_to_finset, Set.mem_set_of_eq]

noncomputable def values (f : α ▸ β) : Finset β :=
  let description := { v | ∃ i, f i = some v }
  let finite : description.finite := by
    let s := f.ids.image f.lookup
    let t := { v | ∃ i, f i = some v }.image Option.some
    suffices h : t ⊆ ↑s by
      exact Set.finite.subset (Finset.finite_to_set s) h
    intro x h
    simp at *
    match h with
    | ⟨b, ⟨a, ha⟩, hb⟩ =>
      exists a
      rw [idsDef]
      split
      simp [ha]
      simp [ha, hb]
  finite.toFinset

theorem valuesDef {f : α ▸ β} {v : β} : v ∈ f.values ↔ (∃ i, f i = some v) := by
  simp [values, Set.finite.mem_to_finset, Set.mem_set_of_eq]

def map (f : α ▸ β) (g : β → γ) : Finmap α γ := {
  lookup := λ i => (f i) >>= (some ∘ g),
  finite := by
    suffices h : { a | (λ i => (f i) >>= (some ∘ g)) a ≠ none } ⊆ ↑f.ids by 
      exact Set.finite.subset (Finset.finite_to_set _) h
    simp
    intro x h
    match h with
    | ⟨v, ⟨b, ⟨hb, hv⟩⟩⟩ =>
      simp [idsDef, Option.ne_none_iff_exists, hb]
}

example (o : Option α) (a : α) (h : a ∈ o) : True := True.intro

end Finmap