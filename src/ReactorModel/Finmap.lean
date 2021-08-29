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
  emptyCollection := {
    lookup := (λ _ => none),
    finite := by
      /-
      by_cases h : (Set.univ : Set α).nonempty
      case pos => simp [Set.nonempty.image_const h Option.none]
      case neg => 
        simp only [Set.not_nonempty_iff_eq_empty] at h
        simp [h, Set.image_empty]
      -/
      sorry
  }  

instance : Inhabited (Finmap α β) where
  default := ∅

noncomputable def ids (f : α ▸ β) : Finset α :=
  let description := { i | f i ≠ none }
  let finite : description.finite := sorry
  finite.toFinset

theorem idsDef {f : α ▸ β} {i : α} : i ∈ f.ids ↔ f i ≠ none := by
  simp [ids, Set.finite.mem_to_finset, Set.mem_set_of_eq]

noncomputable def values (f : α ▸ β) : Finset β :=
  let description := { v | ∃ i, f i = some v }
  let finite : description.finite := sorry
  finite.toFinset

def map (f : α ▸ β) (g : β → γ) : Finmap α γ := {
  lookup := λ i => (f i) >>= (g .),
  finite := by
    /-let s : Finset γ := f.values.image g
    suffices h : ↑s = { v : γ | ∃ i, (λ i => (f i) >>= (g .)) i = some v } by 
      have h' := @finiteValues _ _ (λ i => (f i) >>= (λ j => some (g j)))
      rw [←h] at h'
      simp only [Finset.finite_to_set] at h'
      exact (h'.mp True.intro)
    apply Set.ext
    intro x
    -/
    sorry
}

end Finmap