import ReactorModel.Mathlib.Multiset

structure Finset (α) where
  val : Multiset α
  nodup : Multiset.nodup val

def Multiset.toFinset [DecidableEq α] (s : Multiset α) : Finset α := ⟨_, nodupEraseDup s⟩

namespace Finset

instance : Mem α (Finset α) := ⟨λ a f => a ∈ f.val⟩

instance : EmptyCollection (Finset α) := ⟨{ val := ∅, nodup := Multiset.nodupEmpty }⟩

instance : Inhabited (Finset α) where
  default := ∅

protected def bUnion [DecidableEq β] (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.val.bind (λ a => (t a).val)).toFinset

def singleton (a : α) : Finset α := ⟨[a], sorry⟩

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

end Finset