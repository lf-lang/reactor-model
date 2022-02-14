import ReactorModel.Mathlib.Finset

namespace Set 

theorem ext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := sorry

theorem ext_iff {x y : Set α} : (∀ z : α, z ∈ x ↔ z ∈ y) ↔ x = y := sorry

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

theorem finite_option {s : Set (Option α)} : finite s ↔ finite {x : α | some x ∈ s} := sorry

@[simp] theorem mem_image (f : α → β) (s : Set α) (y : β) :
  y ∈ s.image f ↔ ∃ x, x ∈ s ∧ f x = y := sorry

theorem finite.subset {s : Set α} : finite s → ∀ {t : Set α}, t ⊆ s → finite t := sorry

theorem subset_def {s t : Set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := sorry

theorem mem_union (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := sorry

end Set

theorem Finset.finite_to_set (s : Finset α) : Set.finite (↑s : Set α) := sorry