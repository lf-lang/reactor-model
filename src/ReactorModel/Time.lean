import Mathlib

def Time := Nat
deriving LinearOrder, Ord, DecidableEq, Inhabited

namespace Time
 
structure Tag where 
  t : Time
  microsteps : Nat

-- TODO: Replace this with `deriving LinearOrder` once that feature is available again.
instance : LinearOrder Tag := sorry
  
end Time