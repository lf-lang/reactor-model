namespace Time

def Time :=  Nat
  deriving Ord, DecidableEq, LE, LT

-- These should be derivable automatically, shouldn't they?
instance Time.decLe (n m : @& Time) : Decidable (LE.le n m) :=
  dite (Eq (Nat.ble n m) true) (fun h => isTrue (Nat.le_of_ble_eq_true h)) (fun h => isFalse (Nat.not_le_of_not_ble_eq_true h))

instance Time.decLt (n m : @& Time) : Decidable (LT.lt n m) :=
  decLe (Nat.succ n) m
 
structure Tag where 
  mk :: (t : Time) (microsteps : Nat)


def advance (g : Tag) (t : Time) : Option Tag :=  
 match g with 
  | Tag.mk gt gm => if (gt = t) 
  then some (Tag.mk t (gm+1))
  else if (t < gt) then none 
  else some (Tag.mk t 0)

end Time