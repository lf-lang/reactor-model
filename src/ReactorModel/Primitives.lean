import ReactorModel.Mathlib

open Classical

constant ID : Type

constant _Value : Σ V : Type, V := Sigma.mk Unit Unit.unit
def Value : Type _ := _Value.fst
constant Value.absent : Value := _Value.snd

notation "⊥" => Value.absent

inductive Rooted (ID)
  | root
  | nest (i : ID)

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

-- Port roles are used to differentiate between input and output ports.
-- This is useful for avoiding duplication of definitions that are fundamentally 
-- the same and only differ by the kinds of ports that are referenced/affected.
--
-- E.g. a reaction defines its dependencies as a map `Port.Role → Finset ID`,
-- instead of two separate fields, each of type `Finset ID`.
inductive Port.Role
  | «in» 
  | out
deriving DecidableEq

-- When writing functions that are generic over a port's role,
-- it is sometimes necessary to talk about the "opposite" role.
--
-- E.g. when connecting ports, it might be possible to connect an
-- input to an output port, as well as an output port to an input port.
-- This can be defined generically by using the concept of an opposite role.
abbrev Port.Role.opposite : Role → Role 
  | Role.in => Role.out
  | Role.out => Role.in

structure Port where
  role : Port.Role
  val : Value

namespace Finmap 

-- TODO: Remove `get`, `eqAt` and `inhabitedIDs` if they remain unused.

-- A lookup method for ports where the absent value is treated as the absence of a value.
--
-- Since ports are just finmaps, they inherit its `lookup` function.
-- As a result, if a given port `i` contains the absent value (`⊥`), then `p.lookup i = some ⊥`.
-- In many definitions we only care to differentiate between two cases though:
--
-- (1) `p.lookup i = some v` with `v ≠ ⊥`.
-- (2) `p.lookup i = some ⊥` or `p.lookup i = none`.
-- 
-- The `get` function provides this case separation by mapping `some ⊥` to `none`.
-- That is, if `p.get i = some v`, we know `v ≠ ⊥`.
--
-- The notation used for `p.get i` is `p[i]`.
noncomputable def getValue (p : ID ⇉ Value) (i : ID) : Option Value := 
  p.lookup i >>= (λ v => if v = ⊥ then none else v)

notation p:max "[" i "]" => getValue p i

theorem eq_lookup_eq_getValue {p₁ p₂ : ID ⇉ Value} {i : ID} (h : p₁ i = p₂ i) :
  p₁[i] = p₂[i] := by
  simp [getValue, bind, h]

theorem lookup_none_getValue_none {p : ID ⇉ Value} {i : ID} (h : p i = none) : 
  p[i] = none := by
  simp only [getValue, h]

theorem lookup_absent_getValue_none {p : ID ⇉ Value} {i : ID} (h : p i = some ⊥) :
  p[i] = none := by
  simp [getValue, bind, Option.bind, h]

-- Two port-assignments are `eqAt` (equal at) a given set of IDs,
-- if their values correspond for all those IDs.
-- Note, we only require equality up to `get`, not `lookup`.
--
-- The notation used for `eqAt is p₁ p₂` is `p₁ =[is] p₂`.
def eqAt (is : Finset ID) (p₁ p₂ : ID ⇉ Value) : Prop := 
  ∀ i ∈ is, p₁[i] = p₂[i]

notation p:max " =[" i "] " q:max => eqAt i p q

-- (For a fixed set of IDs) `eqAt` is an equivalence relation.
instance eqAt.Setoid (is : Finset ID) : Setoid (ID ⇉ Value) := { 
  r := eqAt is,
  iseqv := { 
    refl := by simp [eqAt]
    symm := by
      simp only [eqAt]
      intro _ _ h i hi
      exact (h i hi).symm
    trans := by
      simp only [eqAt]
      intro _ _ _ hxy hyz i hi
      exact Eq.trans (hxy i hi) (hyz i hi)
  }
}

-- An ID "is present" in a port assignment if the port exists and has a non-absent value.
-- That is, it contains a value that is not `⊥`.
def isPresent (p : ID ⇉ Value) (i : ID) : Prop :=
  p[i] ≠ none

-- The (finite) set of IDs for which a given port-assignment contains non-absent values.
noncomputable def presentIDs (p : ID ⇉ Value) : Finset ID :=
  let description : Set ID := { i | p.isPresent i }
  let finite : description.finite := by
    let f : Finset ID := p.ids.filter (λ i => p[i] ≠ none)
    suffices h : description ⊆ ↑f 
      from Set.finite.subset (Finset.finite_to_set _) h
    simp [Set.subset_def]
    intro x h
    simp at *
    constructor
    case right => exact h
    case left =>
      rw [Finmap.ids_def, Ne.def]
      exact mt lookup_none_getValue_none h  
  finite.toFinset

end Finmap