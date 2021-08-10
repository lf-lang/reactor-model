import Mathlib

namespace Option 

protected def elim : Option α → β → (α → β) → β
  | (some x), y, f => f x
  | none,     y, f => y

instance : Bind (Option) := ⟨Option.bind⟩

instance : Mem α (Option α) := ⟨λ a b => b = some a⟩

lemma ne_none_iff_exists {o : Option α} : 
  o ≠ none ↔ ∃ (x : α), some x = o := 
  sorry

lemma bind_eq_bind {f : α → Option β} {x : Option α} :
  x >>= f = x.bind f := 
  rfl

@[simp] theorem bind_eq_some {x : Option α} {f : α → Option β} {b : β} :
  x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b := 
  sorry

@[simp] theorem bind_eq_none {o : Option α} {f : α → Option β} :
  o >>= f = none ↔ (∀ b a, a ∈ o → b ∉ f a) := 
  sorry

end Option