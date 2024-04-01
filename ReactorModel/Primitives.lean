import ReactorModel.Extensions

noncomputable section
open Classical

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

inductive Value.IsPresent : Value → Prop
  | intro : IsPresent (present val)

-- We use IDs to reference various kinds of components like ports, reactions, actions, etc.
-- The precise nature of IDs is not relevant, which is why we define the type as `opaque`.
opaque ID : Type

-- Note: This approach is also used in the implementation of Lean:
--       https://github.com/leanprover/lean4/blob/b81cff/src/Lean/Environment.lean#L18
opaque PrioritySpec : (p : Type) × (PartialOrder p) := ⟨Unit, inferInstance⟩ 

-- The `Priority` type is used to impose a (potentially partial) order on reactions.
def Priority := PrioritySpec.fst

instance : PartialOrder Priority := PrioritySpec.snd

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

def Time := Nat
deriving LinearOrder

instance : OfNat Time 0 where
  ofNat := .zero

-- A `Time.Tag` is used to represent a logical time tag.
-- The order of these tags is lexicographical with the `time` taking priority.
@[ext]
structure Time.Tag where 
  time : Time
  microstep : Nat
  
namespace Time.Tag

instance : LE Time.Tag where
  le g₁ g₂ := (g₁.time < g₂.time) ∨ (g₁.time = g₂.time ∧ g₁.microstep ≤ g₂.microstep)

-- TODO: Use deriving one this once the feature lands in mathlib:
--       https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Lexicographical.20LinearOrder
instance : LinearOrder Time.Tag where
  le_refl g := .inr ⟨rfl, le_refl _⟩
  le_trans _ _ _
    | .inl h₁, .inl h₂ => .inl $ h₁.trans h₂
    | .inl h₁, .inr ⟨h₂, _⟩ | .inr ⟨h₂, _⟩, .inl h₁ => .inl $ h₂ ▸ h₁
    | .inr ⟨h₁, h₁'⟩, .inr ⟨h₂, h₂'⟩ => .inr ⟨h₁.trans h₂, h₁'.trans h₂'⟩ 
  le_antisymm := by
    intro _ _; intro
    | .inl h₁, .inl h₂ => exact absurd h₁ h₂.asymm
    | .inl h₁, .inr ⟨h₂, _⟩ | .inr ⟨h₂, _⟩, .inl h₁ => exact absurd (h₂ ▸ h₁) (lt_irrefl _)
    | .inr ⟨h₁, h₁'⟩, .inr ⟨h₂, h₂'⟩ => exact Time.Tag.ext _ _ (h₁ ▸ h₂) (h₁'.antisymm h₂') 
  le_total := by 
    intro ⟨t₁, m₁⟩ ⟨t₂, m₂⟩
    by_cases ht : t₁ = t₂ <;> by_cases hm : m₁ = m₂ <;> simp_all
    · exact .inr ⟨rfl, le_rfl⟩ 
    · cases Nat.le_total m₁ m₂
      · exact .inl $ .inr ⟨rfl, ‹_›⟩
      · exact .inr $ .inr ⟨rfl, ‹_›⟩  
    all_goals
      cases Nat.le_total t₁ t₂
      · exact .inl $ .inl $ lt_of_le_of_ne ‹_› ht
      · exact .inr $ .inl $ lt_of_le_of_ne ‹_› (ht ·.symm)
  decidableLE := inferInstance
  decidableEq := inferInstance

instance : OfNat Time.Tag 0 where
  ofNat := ⟨0, 0⟩ 

end Time.Tag  


