import ReactorModel.Mathlib

-- A `PresentValue` is a non-absent value.
-- We use this is `Value` to define the complete type of values.
private opaque PresentValue : Type

-- `Value`s are the objects that are consumed and produced by reactions
-- and passed along via ports and actions.
-- The `absent` value is a special value which is used with ports to 
-- represent that a given port is not populated with a value.
inductive Value 
  | absent 
  | present (val : PresentValue)

-- A value is considered "present" if it is not the absent value.
def Value.isPresent : Value → Bool 
  | absent => false
  | present _ => true

-- We use IDs to reference various kinds of components like ports, reactions, actions, etc.
-- The precise nature of IDs is not relevant, which is why we define the type as `opaque`.
opaque ID : Type

-- The type of `RootedID`s extends the type of `ID`s with a `root` ID.
-- The `root` ID is used to refer to a/the top level reactor.
-- All other IDs are called "nested" IDS as they are used to refer to 
-- components which are nested inside the top level reactor (arbitrarily deep).
--
-- We don't include the `root` ID in the normal `ID` type, as most contexts
-- require that the `root` ID cannot not be used. For example, it should
-- not be possible for a reaction to be identified by the `root` ID. 
-- We therefore use the `ID` type  instead of the `RootedID` type to 
-- identify reactions.
inductive RootedID
  | root
  | nest (i : ID)

notation "⊤" => RootedID.root

-- Any normal `ID` can be coerced to a `RootedID`.
instance : Coe ID (RootedID) := ⟨RootedID.nest⟩

-- Returns the nested `ID` contained in the `RootedID` if possible. 
def RootedID.nest? : RootedID → Option ID
  | ⊤ => none
  | nest i => i

-- The `nest?` function is injective (technically even bijective) 
-- as a return value of `none` is unique to `RootedID.root`.
theorem RootedID.nest?_inj : nest?.injective :=
  λ i j => by cases i <;> cases j <;> simp [nest?]

-- The `Identified` type extends a given type with a rooted ID.
-- We sometimes use this when we want to pass around a component 
-- along with its ID. For example, the `Reactor.con?` function 
-- returns an `Identified Reactor`.
@[ext]
structure Identified (α) where
  id : RootedID
  obj : α

-- Any `Identified α` can be coerced back to an `α`.
instance : CoeHead (Identified α) α := ⟨Identified.obj⟩

-- The `Priority` type is used to impose a (potentially partial) 
-- order on reactions. The order of priorities is given by the
-- order on `Nat` with the addition that a priority of `none` is
-- incomparable to all priorities.
def Priority := Option Nat

-- The order of priorities is given by the order on `Nat` with the
-- addition that a priority of `none` is incomparable to all priorities.
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

-- The `Kind` type is used to generically distinguish between things which
-- have an "input" and "output" variant. This is the case for ports as well
-- as ports' dependencies. 
inductive Kind
  | «in» 
  | out
deriving DecidableEq

-- When writing functions that are generic over a kind,
-- it is sometimes convenient to talk about the "opposite" kind.
abbrev Kind.opposite : Kind → Kind
  | .in => .out
  | .out => .in

-- Ports are the interface points of reactors, by which they can exchange values.
-- There are two kinds of ports: input and output ports.
-- The resulting definition reflects precisely these two aspects:
structure Port where
  val : Value
  kind : Kind

def Time := Nat
deriving LinearOrder, Ord, DecidableEq, Inhabited

-- A `Time.Tag` is used to represent a logical time tag.
-- The order of these tags is lexicographical with the `time` taking priority.
structure Time.Tag where 
  time : Time
  microstep : Nat

-- TODO: Replace this with `deriving LinearOrder` once that feature is available again.
instance : LinearOrder Time.Tag := sorry
