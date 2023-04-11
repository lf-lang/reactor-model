import ReactorModel.Objects.Reactor.Theorems.Indexable
import ReactorModel.Objects.Reactor.Theorems.WellFounded

namespace ReactorType

class WellIndexable (α) extends Indexable α, WellFounded α

variable [WellIndexable α] {rtr : α}

namespace LawfulMemUpdate

open Indexable
variable [WellIndexable α] {rtr₁ : α}

theorem obj?_some₁ (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : ∃ o, rtr₁[cpt][i] = some o := by
  induction u 
  case final         => exact ⟨_, get?_some_to_obj?_some ‹_›⟩
  case nest h _ _ hi => exact ⟨_, obj?_some_nested h hi.choose_spec⟩

theorem obj?_some₂ (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : ∃ o, rtr₂[cpt][i] = some o := by
  induction u 
  case final       => exact ⟨_, get?_some_to_obj?_some ‹_›⟩
  case nest h _ hi => exact ⟨_, obj?_some_nested h hi.choose_spec⟩

theorem obj?_some_iff (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    (∃ o, rtr₁[c][j] = some o) ↔ (∃ o, rtr₂[c][j] = some o) :=
  Equivalent.obj?_some_iff u.equiv

theorem obj?_none_iff (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    (rtr₁[c][j] = none) ↔ (rtr₂[c][j] = none) :=
  Equivalent.obj?_none_iff u.equiv

/-
-- TODO: This is a general (perhaps very important) theorem about obj?.
theorem obj?_some_elim {rtr : α} {i : ID} (h : rtr[cpt][i] = some o) : (rtr{cpt}{i} = some o) ∨ (∃ j con, rtr{.rtr}{j} = some con ∧ con[cpt][i] = some o) :=
  sorry
  -- This should be derivable directly from obj?_to_con?_and_cpt?
-/

theorem obj?_preserved (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) (h : c ≠ cpt ∨ j ≠ i) : 
    rtr₂[c][j] = rtr₁[c][j] := by
  cases ho₁ : rtr₁[c][j]
  case none => sorry -- simp [u.obj?_none_iff.mp ho₁]
  case some =>
    sorry
    /-
    have ⟨_, ho₂⟩ := u.obj?_some_iff.mp ⟨_, ho₁⟩ 
    simp [ho₂]

    -- TODO: We need to somehow distinguish whether [c][j] lives in the same reactor as [cpt][i].
    induction u
    case final e _ _ =>
      cases obj?_some_elim ho₁ <;> cases obj?_some_elim ho₂
      case inl.inl h₁ h₂ =>
        injection h₁ ▸ h₂ ▸ e (c := c) (j := j) (by simp [h]) with h
        exact h.symm
      case inr.inr h₁ h₂ =>
        obtain ⟨j₁, con₁, hn₁, hc₁⟩ := h₁
        obtain ⟨j₂, con₂, hn₂, hc₂⟩ := h₂
        simp at hc₁ hc₂
        have hj : j₁ = j₂ := sorry 
        subst hj
        have hn := e (c := .rtr) (j := j₁) (by simp [h])
        injection hn₂ ▸ hn ▸ hn₁ with h
        subst h
        injection hc₁ ▸ hc₂ with h
        exact h.symm
      case inl.inr =>
        simp at * -- contra
        sorry
      case inr.inl =>
        simp at * -- contra
        sorry
    case nest =>
      sorry
    -/

theorem obj?_updated (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    rtr₂[cpt][i] = f <$> rtr₁[cpt][i] := by
  induction u
  case final h₁ h₂ => 
    rw [get?_some_to_obj?_some h₁, get?_some_to_obj?_some h₂, Option.map_some]
  case nest h₁ h₂ u hi =>
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
  | update u => u.obj?_updated
  | notMem h e => by subst e; simp [member_isEmpty_obj?_none h]

end LawfulUpdate
end ReactorType
