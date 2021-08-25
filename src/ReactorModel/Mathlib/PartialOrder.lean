import Mathlib

instance (α) : Inhabited (PartialOrder α) where
  default := { 
    le := sorry,
    le_refl := sorry,
    lt := sorry,
    le_trans := sorry,
    lt_iff_le_not_le := sorry,
    le_antisymm := sorry,
  }