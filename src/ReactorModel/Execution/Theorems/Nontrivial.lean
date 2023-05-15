import ReactorModel.Execution.Theorems.TimeStep
import ReactorModel.Execution.Theorems.TimeStep

open ReactorType Classical

namespace Execution

variable [Indexable α] {s s₁ s₂ : State α}

namespace State

def Nontrivial (s : State α) : Prop :=
  s.rtr[.rcn].Nonempty

theorem Nontrivial.equiv (e : s₁.rtr ≈ s₂.rtr) (n : s₁.Nontrivial) : s₂.Nontrivial := by
  simp_all [Nontrivial, Equivalent.obj?_rcn_eq e]

theorem Closed.progress_nonempty (n : s.Nontrivial) (h : Closed s) : s.progress.Nonempty := by
  simp_all [Closed, ←Partial.Nonempty.iff_ids_nonempty]
  exact n

end State

namespace Step

theorem Skip.preserves_nontrivial {e : s₁ ↓ₛ s₂} (n : s₁.Nontrivial) : s₂.Nontrivial :=
  n.equiv sorry -- e.equiv

theorem Exec.preserves_nontrivial {e : s₁ ↓ₑ s₂} (n : s₁.Nontrivial) : s₂.Nontrivial :=
  n.equiv sorry -- e.equiv

namespace Time

theorem preserves_nontrivial {e : s₁ ↓ₜ s₂} (n : s₁.Nontrivial) : s₂.Nontrivial :=
  n.equiv e.equiv

theorem not_closed (e : s₁ ↓ₜ s₂) (n : s₁.Nontrivial) : ¬s₂.Closed :=
  (·.progress_nonempty (e.preserves_nontrivial n) |>.ne_empty e.progress_empty)

theorem nonrepeatable (e₁ : s₁ ↓ₜ s₂) (e₂ : s₂ ↓ₜ s₃) (n : s₁.Nontrivial) : False :=
  e₁.not_closed n e₂.closed

end Time

instance preserves_nontrivial (n : s₁.Nontrivial) : (s₁ ↓ s₂) → s₂.Nontrivial
  | skip e | exec e | time e => e.preserves_nontrivial n

end Step

/-namespace Step

theorem seq_tag_lt (n : s₁.Nontrivial) : (s₁ ⇓ s₂) → (s₂ ⇓ s₃) → s₁.tag < s₃.tag
  | close e₁,   close e₂   => e₁.nonrepeatable e₂ |>.elim
  | advance a₁, advance a₂ => a₁.nonrepeatable a₂ n |>.elim
  | close e,    advance a  => e.preserves_tag ▸ a.tag_lt
  | advance a,  close e    => e.preserves_tag ▸ a.tag_lt

end Step

-- TODO: This doesn't require nontrivial.
theorem tag_le {s₁ s₂ : State α} (e : s₁ ⇓ s₂) : s₁.tag ≤ s₂.tag := by
  induction e with
  | refl        => exact le_refl _
  | step e _ hi => exact le_trans e.tag_le hi
-/

/-
theorem nontrivial_deterministic {s s₁ s₂ : State α} (n : s.Nontrivial)
    (e₁ : s ⇓ s₁) (e₂ : s ⇓ s₂) (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) : 
    s₁ = s₂ := by
  induction e₁ generalizing s₂ <;> cases e₂
  case refl.refl => rfl
  case trans.trans e₁ _ hi _ e₂ e₂' =>
    exact hi (e₁.preserves_nontrivial n) (e₁.deterministic e₂ ▸ e₂') ht hp
  all_goals
    have e := ‹_ ↓  _›; have e' := ‹_ ⇓ _›
    exact match seq_progress_ssubset_or_tag_lt n e e' with
    | .inl h => absurd hp (Set.ssubset_ne $ by simp_all) 
    | .inr h => absurd ht $ ne_of_lt (by simp_all)
-/

end Execution