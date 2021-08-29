import ReactorModel.Mathlib.Finset

namespace Set 

theorem ext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := sorry

@[simp] theorem mem_sep_eq {s : Set α} {p : α → Prop} {x : α} : 
  x ∈ {x ∈ s | p x} ↔ (x ∈ s ∧ p x) := sorry

@[simp] theorem mem_set_of_eq {a : α} {p : α → Prop} : a ∈ {a | p a} ↔ p a := sorry

def finite (s : Set α) : Prop := sorry

noncomputable def finite.toFinset {s : Set α} (h : s.finite) : Finset α := sorry

theorem finite.mem_to_finset {s : Set α} (h : finite s) {a : α} : a ∈ h.toFinset ↔ a ∈ s := sorry

protected def nonempty (s : Set α) : Prop := ∃ x, x ∈ s

@[simp] theorem nonempty.image_const {s : Set α} (hs : s.nonempty) (a : β) : s.image (λ _ => a) = {a} := sorry

theorem not_nonempty_iff_eq_empty {s : Set α} : ¬s.nonempty ↔ s = ∅ := sorry

@[simp] theorem image_empty (f : α → β) : (∅ : Set α).image f = ∅ := sorry

@[simp] theorem finite_empty : @finite α ∅ := sorry

@[simp] theorem finite_singleton (a : α) : finite ({a} : Set α) := sorry

end Set

theorem Finset.finite_to_set (s : Finset α) : Set.finite (↑s : Set α) := sorry