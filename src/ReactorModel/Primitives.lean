import ReactorModel.Mathlib

private constant PresentValue : Type

inductive Value 
  | absent 
  | present (val : PresentValue)

notation "⊥" => Value.absent

def Value.isPresent : Value → Bool 
  | absent => false
  | present _ => true

constant ID : Type

inductive Rooted (ι)
  | root
  | nest (i : ι)

notation "⊤" => Rooted.root

instance : Coe ID (Rooted ID) := ⟨Rooted.nest⟩

def Rooted.nest? : Rooted ID → Option ID
  | ⊤ => none
  | nest i => i

theorem Rooted.nest?_inj : nest?.injective :=
  λ i j => by cases i <;> cases j <;> simp [nest?]

structure Identified (α) where
  id : Rooted ID
  obj : α

instance : CoeHead (Identified α) α := ⟨Identified.obj⟩

instance : Membership α (List $ Identified α) where 
  mem a as := a ∈ as.map (·.obj)

def Priority := Option Nat

instance : PartialOrder Priority := {
  le := λ p₁ p₂ => p₁ = p₂ ∨ ∃ v₁ v₂, p₁ = some v₁ ∧ p₂ = some v₂ ∧ v₁ ≤ v₂,
  le_refl := by simp [LE.le], 
  le_trans := by
    intro p₁ p₂ p₃ h₁₂ h₂₃
    simp only [LE.le] at *
    cases h₁₂ <;> cases h₂₃
    case inl.inl h₁₂ h₂₃ => simp [h₁₂, h₂₃]
    case inl.inr h₁₂ h₂₃ => rw [h₁₂]; exact Or.inr h₂₃ 
    case inr.inl h₁₂ h₂₃ => rw [←h₂₃]; exact Or.inr h₁₂
    case inr.inr h₁₂ h₂₃ =>
      have ⟨v₁, v₂, h₁₂⟩ := h₁₂
      have ⟨v₂', v₃, h₂₃⟩ := h₂₃
      have h₂ := h₁₂.right.left
      rw [h₂₃.left] at h₂
      rw [Option.some_inj.mp h₂] at h₂₃
      have h := Nat.le_trans h₁₂.right.right h₂₃.right.right
      exact Or.inr ⟨v₁, v₃, ⟨h₁₂.left, ⟨h₂₃.right.left, h⟩⟩⟩,
  lt_iff_le_not_le := by simp [LT.lt, LE.le],
  le_antisymm := by
    intro p₁ p₂ h₁₂ h₂₁
    simp only [LE.le] at *
    cases h₁₂ <;> cases h₂₁
    case' inl.inl h, inl.inr h _, inr.inl h => simp only [h]
    case inr.inr h₁₂ h₂₁ =>  
      have ⟨v₁, v₂, h₁₂⟩ := h₁₂
      have ⟨v₂', v₁', h₂₁⟩ := h₂₁
      rw [h₁₂.left, h₁₂.right.left] at h₂₁ ⊢
      have h₁ := Option.some_inj.mp h₂₁.left
      have h₂ := Option.some_inj.mp h₂₁.right.left
      rw [←h₁, ←h₂] at h₂₁
      exact Option.some_inj.mpr $ Nat.le_antisymm h₁₂.right.right h₂₁.right.right
}

inductive Kind
  | «in» 
  | out
deriving DecidableEq

-- When writing functions that are generic over a port's kind,
-- it is sometimes necessary to talk about the "opposite" kind.
--
-- E.g. when connecting ports, it might be possible to connect an
-- input to an output port, as well as an output port to an input port.
-- This can be defined generically by using the concept of an opposite kind.
abbrev Kind.opposite : Kind → Kind
  | .in => .out
  | .out => .in

structure Port where
  val : Value
  kind : Kind

def Time := Nat
deriving LinearOrder, Ord, DecidableEq, Inhabited

structure Time.Tag where 
  t : Time
  microsteps : Nat

-- TODO: Replace this with `deriving LinearOrder` once that feature is available again.
instance : LinearOrder Tag := sorry
