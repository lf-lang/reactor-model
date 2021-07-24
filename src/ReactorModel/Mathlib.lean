import Mathlib.Data.List.Basic

namespace List

variable (r : α → α → Prop)

inductive Pairwise : List α → Prop
  | nil : Pairwise []
  | cons : ∀ {a : α} {l : List α}, (∀ a' ∈ l, r a a') → Pairwise l → Pairwise (a::l)

def Nodup : List α → Prop := Pairwise (. ≠ .)

inductive Perm : List α → List α → Prop
  | nil   : Perm [] []
  | cons  : ∀ (x : α) {l₁ l₂ : List α}, Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
  | swap  : ∀ (x y : α) (l : List α), Perm (y::x::l) (x::y::l)
  | trans : ∀ {l₁ l₂ l₃ : List α}, Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

infix:50 " ~ " => Perm

protected theorem Perm.refl : ∀ (l : List α), l ~ l
  | []      => Perm.nil
  | (x::xs) => (Perm.refl xs).cons x

protected theorem Perm.symm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₂ ~ l₁ := by
  induction p with
  | nil => exact nil
  | cons x _ p => exact cons x p
  | swap x y l => exact swap y x l
  | trans _ _ p₁ p₂ => exact trans p₂ p₁

theorem Perm.eqv : Equivalence (@Perm α) where
  refl := Perm.refl
  symm := Perm.symm
  trans := Perm.trans

instance isSetoid (α) : Setoid (List α) :=
  Setoid.mk _ Perm.eqv

theorem Perm.lengthEq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ h => simp [h]
  | swap => simp
  | trans _ _ h₁ h₂ => exact Eq.trans h₁ h₂

theorem Perm.eqNil {l : List α} (p : l ~ []) : l = [] :=
  eq_nil_of_length_eq_zero p.lengthEq

theorem Perm.nilEq {l : List α} (p : [] ~ l) : [] = l :=
  p.symm.eqNil.symm

theorem Perm.subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ := by
sorry

theorem Perm.pairwiseIff {R : α → α → Prop} (S : ∀ {x y}, R x y → R y x) :
  ∀ {l₁ l₂ : List α} (p : l₁ ~ l₂), Pairwise R l₁ ↔ Pairwise R l₂ := by
  suffices ∀ {l₁ l₂}, l₁ ~ l₂ → Pairwise R l₁ → Pairwise R l₂ 
  from λ l₁ l₂ p => ⟨this p, this p.symm⟩
  intro l₁ l₂ p d
  induction d generalizing l₂ with
  | nil => 
    rw [←p.nilEq]
    constructor
  | @cons a l₁ h d IH =>
    have : a ∈ l₂ := p.subset (mem_cons_self _ _)
    sorry
    /-
    rcases mem_split this with ⟨s₂, t₂, rfl⟩,
    have p' := (p.trans perm_middle).cons_inv,
    refine (pairwise_middle S).2 (pairwise_cons.2 ⟨λ b m, _, IH _ p'⟩),
    exact h _ (p'.symm.subset m)
    -/

theorem Perm.nodupIff {l₁ l₂ : List α} : l₁ ~ l₂ → (List.Nodup l₁ ↔ List.Nodup l₂) :=
  Perm.pairwiseIff $ Ne.symm

end List

def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

def Multiset.Nodup (s : Multiset α) : Prop :=
  Quot.liftOn s List.Nodup (λ _ _ p => propext p.nodupIff)

structure Finset (α) where
  val : Multiset α
  nodup : Multiset.Nodup val