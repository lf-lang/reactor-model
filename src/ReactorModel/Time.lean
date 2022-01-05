import Mathlib

def Time := Nat
  deriving LinearOrder, Ord, DecidableEq, Inhabited

namespace Time
 
structure Tag where 
  t : Time
  microsteps : Nat

open Ordering in
def advance (g : Tag) (t : Time) : Option Tag :=  
  match compare g.t t with
  | lt => some ⟨t, 0⟩
  | eq => some ⟨t, g.microsteps + 1⟩
  | gt => none
  
end Time