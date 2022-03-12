import ReactorModel.Mathlib.Multiset

structure Finset (α) where
  val : Multiset α
  nodup : Multiset.nodup val

def Multiset.toFinset [DecidableEq α] (s : Multiset α) : Finset α := ⟨_, nodupEraseDup s⟩

namespace Finset

instance : Membership α (Finset α) := ⟨λ a f => a ∈ f.val⟩

instance : Union (Finset α) := sorry

instance : Inter (Finset α) := sorry

instance : EmptyCollection (Finset α) := ⟨{ val := ∅, nodup := Multiset.nodupEmpty }⟩

instance : Inhabited (Finset α) where
  default := ∅

def insert : Finset α → α → Finset α := sorry

def nonempty (s : Finset α) : Prop := ∃ x : α, x ∈ s

protected def bUnion [DecidableEq β] (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.val.bind (λ a => (t a).val)).toFinset

def image (f : α → β) (s : Finset α) : Finset β := sorry

def singleton (a : α) : Finset α := ⟨[a], sorry⟩

theorem mem_singleton_self (a : α) : a ∈ (Finset.singleton a) := sorry

theorem not_mem_singleton {a b : α} : ¬(a ∈ Finset.singleton b) ↔ a ≠ b := sorry

instance : Coe (Finset α) (Set α) := ⟨λ f => {x | x ∈ f}⟩

def filter (s : Finset α) (p : α → Prop) [DecidablePred p] : Finset α := sorry

theorem ext_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ := sorry

theorem ext {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ := ext_iff.mpr

def range (n : ℕ) : Finset ℕ := sorry

@[simp] theorem mem_range : m ∈ range n ↔ m < n := sorry

@[simp] theorem mem_coe {a : α} {s : Finset α} : a ∈ (s : Set α) ↔ a ∈ s := sorry

@[simp] theorem coe_filter (p : α → Prop) [DecidablePred p] (s : Finset α) : ↑(s.filter p) = ({x ∈ (↑s : Set α) | p x} : Set α) := sorry

@[simp] theorem mem_filter (p : α → Prop) [DecidablePred p] {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a := sorry

instance : Subset (Finset α) := sorry

theorem subset_iff {s₁ s₂ : Finset α} : s₁ ⊆ s₂ ↔ ∀ {x}, x ∈ s₁ → x ∈ s₂ := sorry

@[simp] theorem subset.refl (s : Finset α) : s ⊆ s := sorry

theorem mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ := sorry

theorem inter_subset_right (s₁ s₂ : Finset α) [DecidableEq α] : s₁ ∩ s₂ ⊆ s₂ := sorry

@[simp] theorem mem_image {s : Finset α} {f : α → β} {b : β} : b ∈ s.image f ↔ ∃ a ∈ s, f a = b := sorry

@[simp] theorem mem_union {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ := sorry

@[simp] theorem mem_bUnion {s : Finset α} {t : α → Finset β} {b : β} [DecidableEq β] : b ∈ s.bUnion t ↔ ∃ a ∈ s, b ∈ t a := sorry

instance : Sdiff (Finset α) := sorry

def max' [LinearOrder α] (s : Finset α) (H : s.nonempty) : α := sorry

def max [LinearOrder α] (s : Finset α) : Option α := sorry

def min [LinearOrder α] (s : Finset α) : Option α := sorry

theorem mem_of_min [LinearOrder α] {s : Finset α} : ∀ {a : α}, a ∈ s.min → a ∈ s := sorry

theorem max'_mem [LinearOrder α] (s : Finset α) (H : s.nonempty) : s.max' H ∈ s := sorry

end Finset

def List.toFinset (l : List α) : Finset α := sorry