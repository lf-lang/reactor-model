import Mathlib

namespace Option 

instance : Bind (Option) := ⟨Option.bind⟩

instance : Membership α (Option α) := ⟨λ a b => b = some a⟩

lemma bind_eq_bind {f : α → Option β} {x : Option α} :
  x >>= f = x.bind f := 
  rfl

end Option