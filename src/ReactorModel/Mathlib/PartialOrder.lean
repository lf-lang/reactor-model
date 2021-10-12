import Mathlib
import ReactorModel.Mathlib.Set

instance (α) : Inhabited (PartialOrder α) where
  default := { 
    le := sorry,
    le_refl := sorry,
    lt := sorry,
    le_trans := sorry,
    lt_iff_le_not_le := sorry,
    le_antisymm := sorry,
  }

namespace PartialOrder

-- The finite set of minimal elements in a given finite set for a given partial order.
noncomputable def minimalsIn (p : PartialOrder α) (s : Finset α) : Finset α :=
  let description := { a | ∀ a' ∈ s, ¬(a' < a) }
  let finite : description.finite := sorry
  finite.toFinset 

-- The finite set of maximal elements in a given finite set for a given partial order.
noncomputable def maximalsIn (p : PartialOrder α) (s : Finset α) : Finset α :=
  let description := { a | ∀ a' ∈ s, ¬(a < a') }
  let finite : description.finite := sorry
  finite.toFinset 

-- Produces a partial order that is equal to the given one, except that a given element
-- `a` is incomparable.
noncomputable def withIncomparable (p : PartialOrder α) (a : α) : PartialOrder α :=
  sorry 

end PartialOrder