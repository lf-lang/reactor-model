import ReactorModel.Mathlib.Set
import ReactorModel.Mathlib.Option

structure Finmap (α β) where
  lookup : α → Option β 
  finite : (Set.univ.image lookup).finite

namespace Finmap

infix:50 " ▸ " => (λ a b => Finmap a b)

instance : CoeFun (α ▸ β) (λ _ => α → Option β) where
  coe f := f.lookup

instance : EmptyCollection (Finmap α β) where
  emptyCollection := Finmap.mk (λ _ => none) sorry

instance : Inhabited (Finmap α β) where
  default := ∅
 
noncomputable def ids (f : α ▸ β) : Finset α :=
  let description := { i | f i ≠ none }
  let finite : description.finite := sorry
  finite.toFinset

theorem idsDef {f : α ▸ β} {i : α} : i ∈ f.ids ↔ f i ≠ none := by
  simp [ids, Set.finite.mem_to_finset, Set.mem_set_of_eq]

noncomputable def values (f : α ▸ β) : Finset β :=
  let description := { v | ∃ i, f i ≠ some v }
  let finite : description.finite := sorry
  finite.toFinset

def map (f : α ▸ β) (g : β → γ) : Finmap α γ := {
  lookup := λ i => (f i) >>= (g .),
  finite := sorry
}

end Finmap