import ReactorModel.Extensions

noncomputable section
open Classical

-- `Value`s are the objects that are consumed and produced by reactions
-- and passed along via ports and actions.
-- The `absent` value is a special value which is used with ports to
-- represent that a given port is not populated with a value.
class Value (ν : Type) where
  absent : ν

instance [Value ν] : Bot ν where
  bot := Value.absent

class Valued (α : Type) where
  Val   : Type
  value : Value Val

attribute [instance] Valued.value

postfix:max "◾" => Valued.Val

class Identifiable (α : Type) where
  protected Id : Type

postfix:max "✦" => Identifiable.Id

class Prioritizable (ρ : Type) where
  Priority : Type
  order    : PartialOrder Priority

attribute [instance] Prioritizable.order

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

instance : OfNat Time n where
  ofNat := n

-- A `Time.Tag` is used to represent a logical time tag.
-- The order of these tags is lexicographical with the `time` taking priority.
@[ext]
structure Time.Tag where
  time : Time
  microstep : Nat

namespace Time.Tag

instance : LE Time.Tag where
  le g₁ g₂ := (g₁.time < g₂.time) ∨ (g₁.time = g₂.time ∧ g₁.microstep ≤ g₂.microstep)

-- TODO: Use `deriving LinearOrder` once this PR lands:
--       https://github.com/leanprover-community/mathlib4/pull/3251
instance : LinearOrder Time.Tag where
  le_refl g := .inr ⟨rfl, le_refl _⟩
  le_trans _ _ _
    | .inl h₁, .inl h₂ => .inl <| h₁.trans h₂
    | .inl h₁, .inr ⟨h₂, _⟩ | .inr ⟨h₂, _⟩, .inl h₁ => .inl <| h₂ ▸ h₁
    | .inr ⟨h₁, h₁'⟩, .inr ⟨h₂, h₂'⟩ => .inr ⟨h₁.trans h₂, h₁'.trans h₂'⟩
  le_antisymm := by
    intro _ _; intro
    | .inl h₁, .inl h₂ => exact absurd h₁ h₂.asymm
    | .inl h₁, .inr ⟨h₂, _⟩ | .inr ⟨h₂, _⟩, .inl h₁ => exact absurd (h₂ ▸ h₁) (lt_irrefl _)
    | .inr ⟨h₁, h₁'⟩, .inr ⟨h₂, h₂'⟩ => exact Time.Tag.ext (h₁ ▸ h₂) (h₁'.antisymm h₂')
  le_total := by
    intro ⟨t₁, m₁⟩ ⟨t₂, m₂⟩
    by_cases ht : t₁ = t₂ <;> by_cases hm : m₁ = m₂ <;> simp_all
    · exact .inr ⟨rfl, le_rfl⟩
    · cases Nat.le_total m₁ m₂
      · exact .inl <| .inr ⟨rfl, ‹_›⟩
      · exact .inr <| .inr ⟨rfl, ‹_›⟩
    all_goals
      cases Nat.le_total t₁ t₂
      · exact .inl <| .inl <| lt_of_le_of_ne ‹_› ht
      · exact .inr <| .inl <| lt_of_le_of_ne ‹_› (ht ·.symm)
  decidableLE := inferInstance
  decidableEq := inferInstance

instance : OfNat Time.Tag 0 where
  ofNat := ⟨0, 0⟩

theorem lt_of_lt_time (h : t₁ < t₂ := by decide) : (⟨t₁, m₁⟩ : Time.Tag) < ⟨t₂, m₂⟩ := by
  simp only [(· < ·), (· ≤ ·)]
  simp_all only [gt_iff_lt, Nat.lt_eq, Nat.le_eq, true_or, not_or, not_lt, not_and, not_le, true_and]
  exact ⟨le_of_lt h, (ne_of_lt h ·.symm |>.elim)⟩

theorem le_to_le_time (h : (⟨t₁, m₁⟩ : Time.Tag) ≤ ⟨t₂, m₂⟩) : t₁ ≤ t₂ := by
  simp only [(· ≤ ·)] at h
  cases h <;> simp_all [le_of_lt]

theorem le_microsteps_of_eq_time {g₁ g₂ : Time.Tag} (h : g₁ ≤ g₂) (ht : g₁.time = g₂.time) :
    g₁.microstep ≤ g₂.microstep := by
  simp only [(· ≤ ·)] at h
  simp_all

theorem lt_microsteps_of_eq_time {g₁ g₂ : Time.Tag} (h : g₁ < g₂) (ht : g₁.time = g₂.time) :
    g₁.microstep < g₂.microstep := by
  simp only [(· < ·), (· ≤ ·)] at h
  simp_all

end Time.Tag
