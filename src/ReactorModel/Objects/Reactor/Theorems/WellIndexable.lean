import ReactorModel.Objects.Reactor.Theorems.Indexable
import ReactorModel.Objects.Reactor.Theorems.WellFounded

namespace ReactorType

class WellIndexable (α) extends Indexable α, WellFounded α

variable [WellIndexable α] {rtr₁ : α}

-- TODO: See comments above `StrictMember.rtr_equiv`.
theorem StrictMember.lawfulMemUpdate_object_preserved 
    (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) (h : c ≠ cpt ∨ j ≠ i) (s₁ : StrictMember c j rtr₁)
    (s₂ : StrictMember c j rtr₂) : s₁.object = s₂.object := by
  induction s₁ generalizing rtr₂ <;> cases s₂ <;> simp [object]
  case final.final h₁ _ h₂ =>
    cases u
    case final e => simp_all [e.valued h]
    case nested e => simp_all [e (c := c) (.inl $ by simp)]
  case nested.nested j₁ _ h₁ s₁ hi j₂ _ s₂ h₂ => 
    have hj : j₁ = j₂ := by 
      have hs := (nested h₁ s₁ |>.fromEquiv u.equiv).unique (nested h₂ s₂)
      simp [fromEquiv] at hs
      exact hs.left
    subst hj
    cases u
    case final e => 
      cases h₂ ▸ (e (c := .rtr) (j := j₁) (.inl $ by simp)) ▸ h₁
      simp [s₁.unique s₂]
    case nested j' _ _ u _ _ e =>
      by_cases hj : j₁ = j'
      case neg => 
        cases h₂ ▸ (e (c := .rtr) (j := j₁) (.inr hj)) ▸ h₁
        simp [s₁.unique s₂]
      case pos => 
        simp_all [hj]
        exact hi (h₁ ▸ h₂ ▸ u) _
  case final.nested h₁ _ _ s₂ h₂ =>
    injection (final h₁ |>.fromEquiv u.equiv).unique (nested h₂ s₂)
  case nested.final h₁ s₁ _ _ h₂ =>
    injection (nested h₁ s₁).unique (final h₂ |>.fromEquiv $ ReactorType.Equivalent.symm u.equiv)     

theorem Member.lawfulMemUpdate_object_preserved 
    (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) (h : c ≠ cpt ∨ j ≠ i) :
    (m₁ : Member c j rtr₁) → (m₂ : Member c j rtr₂) → m₁.object = m₂.object
  | .strict s₁, .strict s₂ => s₁.lawfulMemUpdate_object_preserved u h s₂

namespace LawfulMemUpdate

open Indexable
variable [WellIndexable α] {rtr₁ : α}

theorem obj?_some₁ (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : ∃ o, rtr₁[cpt][i] = some o := by
  induction u 
  case final           => exact ⟨_, get?_some_to_obj?_some ‹_›⟩
  case nested h _ _ hi => exact ⟨_, obj?_some_nested h hi.choose_spec⟩

theorem obj?_some₂ (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : ∃ o, rtr₂[cpt][i] = some o := by
  induction u 
  case final         => exact ⟨_, get?_some_to_obj?_some ‹_›⟩
  case nested h _ hi => exact ⟨_, obj?_some_nested h hi.choose_spec⟩

theorem obj?_some_iff (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    (∃ o, rtr₁[c][j] = some o) ↔ (∃ o, rtr₂[c][j] = some o) :=
  Equivalent.obj?_some_iff u.equiv

theorem obj?_none_iff (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    (rtr₁[c][j] = none) ↔ (rtr₂[c][j] = none) :=
  Equivalent.obj?_none_iff u.equiv

theorem obj?_preserved (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) (h : c ≠ cpt ∨ j ≠ i) : 
    rtr₂[c][j] = rtr₁[c][j] := by
  cases ho₁ : rtr₁[c][j]
  case none => simp [obj?_none_iff u |>.mp ho₁]
  case some =>
    have ⟨_, ho₂⟩ := obj?_some_iff u |>.mp ⟨_, ho₁⟩ 
    have ⟨m₁⟩ := Object.iff_obj?_some.mpr ho₁
    have ⟨m₂⟩ := Object.iff_obj?_some.mpr ho₂
    simp [ho₂, m₁.lawfulMemUpdate_object_preserved u h m₂]

theorem obj?_updated (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    rtr₂[cpt][i] = f <$> rtr₁[cpt][i] := by
  induction u
  case final h₁ h₂ => 
    rw [get?_some_to_obj?_some h₁, get?_some_to_obj?_some h₂, Option.map_some]
  case nested h₁ h₂ u hi =>
    have ⟨_, h₁'⟩ := u.obj?_some₁
    have ⟨_, h₂'⟩ := u.obj?_some₂
    rw [obj?_some_nested h₁ h₁', obj?_some_nested h₂ h₂']
    exact h₁' ▸ h₂' ▸ hi

end LawfulMemUpdate

namespace LawfulUpdate

open Indexable
variable [WellIndexable α] {rtr₁ : α}

theorem obj?_preserved (h : c ≠ cpt ∨ j ≠ i) : 
    (LawfulUpdate cpt i f rtr₁ rtr₂) → rtr₂[c][j] = rtr₁[c][j]
  | update u   => u.obj?_preserved h
  | notMem _ h => h ▸ rfl

theorem obj?_updated : (LawfulUpdate cpt i f rtr₁ rtr₂) → rtr₂[cpt][i] = f <$> rtr₁[cpt][i]
  | update u   => u.obj?_updated
  | notMem h e => by subst e; simp [member_isEmpty_obj?_none h]

end LawfulUpdate
end ReactorType
