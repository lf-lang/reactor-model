import Mathlib

def Time := Nat
  deriving LinearOrder, Ord, DecidableEq, Inhabited

namespace Time
 
structure Tag where 
  t : Time
  microsteps : Nat

instance LinearOrder_Tag : LinearOrder Tag := sorry

open Ordering in
def after (t : Time) (g : Tag) : Option Tag :=  
  match compare t g.t with
  | lt => none
  | eq => some ⟨t, g.microsteps + 1⟩
  | gt => some ⟨t, 0⟩
  
end Time