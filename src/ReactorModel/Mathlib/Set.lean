import ReactorModel.Mathlib.Finset

namespace Set 

theorem ext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := sorry

@[simp] theorem mem_sep_eq {s : Set α} {p : α → Prop} {x : α} : 
  x ∈ {x ∈ s | p x} ↔ (x ∈ s ∧ p x) := sorry

@[simp] theorem mem_set_of_eq {a : α} {p : α → Prop} : a ∈ {a | p a} ↔ p a := sorry

def finite (s : Set α) : Prop := sorry

noncomputable def finite.toFinset {s : Set α} (h : s.finite) : Finset α := sorry

theorem finite.mem_to_finset {s : Set α} (h : finite s) {a : α} : a ∈ h.toFinset ↔ a ∈ s := sorry

end Set

theorem Finset.finite_to_set (s : Finset α) : Set.finite (↑s : Set α) := sorry