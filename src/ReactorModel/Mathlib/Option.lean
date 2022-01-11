import Mathlib

namespace Option 

instance : Bind (Option) := ⟨Option.bind⟩

instance : Mem α (Option α) := ⟨λ a b => b = some a⟩

lemma bind_eq_bind {f : α → Option β} {x : Option α} :
  x >>= f = x.bind f := 
  rfl

def iget [Inhabited α] (a : Option α) : α  :=
match a with
 | (some x) => x
 |  none => arbitrary

end Option