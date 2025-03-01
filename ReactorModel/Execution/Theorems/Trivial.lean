import ReactorModel.Execution.Theorems.Step.Skip
import ReactorModel.Execution.Theorems.Step.Exec
import ReactorModel.Execution.Theorems.Step.Time

open Reactor Classical

variable [Proper α]

namespace Execution

variable {s s₁ : State α} in section

abbrev State.Trivial (s : State α) : Prop :=
  s.rtr[.rcn] = ∅

namespace State.Trivial

theorem equiv {s₁ s₂ : State α} (e : s₁.rtr ≈ s₂.rtr) (t : s₁.Trivial) : s₂.Trivial :=
  Equivalent.obj?_rcn_eq e |>.symm.trans t

theorem of_not_nontrivial (h : ¬Nontrivial s) : s.Trivial :=
  byContradiction (h ·)

end State.Trivial

namespace Step

theorem Skip.not_trivial (e : s₁ ↓ₛ s₂) : ¬s₁.Trivial := by
  by_contra ht
  simp [State.Trivial, Partial.empty_iff] at ht
  cases (Partial.mem_iff.mp e.allows_rcn.mem).choose_spec ▸ ht e.rcn

theorem Exec.not_trivial (e : s₁ ↓ₑ s₂) : ¬s₁.Trivial := by
  by_contra ht
  simp [State.Trivial, Partial.empty_iff] at ht
  cases (Partial.mem_iff.mp e.allows_rcn.mem).choose_spec ▸ ht e.rcn

theorem Time.preserves_trivial (triv : s₁.Trivial) (a : s₁ ↓ₜ s₂) : s₂.Trivial :=
  triv.equiv a.equiv

end Step
end

namespace Step.Time

inductive RTC : State α → State α → Type
  | refl  : RTC s s
  | trans : (s₁ ↓ₜ s₂) → (RTC s₂ s₃) → RTC s₁ s₃

theorem RTC.tag_le {s₁ s₂ : State α} (e : RTC s₁ s₂) : s₁.tag ≤ s₂.tag := by
  induction e with
  | refl         => exact le_refl _
  | trans a _ hi => exact le_trans (le_of_lt a.tag_lt) hi

theorem RTC.deterministic {s s₁ s₂ : State α}
    (ht : s₁.tag = s₂.tag) (e₁ : RTC s s₁) (e₂ : RTC s s₂) : s₁ = s₂ := by
  induction e₁ generalizing s₂ <;> cases e₂
  case refl.refl         => rfl
  case refl.trans e e'   => exact absurd ht      (ne_of_lt <| lt_of_lt_of_le e.tag_lt e'.tag_le)
  case trans.refl e e' _ => exact absurd ht.symm (ne_of_lt <| lt_of_lt_of_le e.tag_lt e'.tag_le)
  case trans.trans e₁ e₁' hi _ e₂ e₂' => exact hi ht (e₂.deterministic e₁ ▸ e₂')

end Step.Time

def to_timeStepRTC {s₁ s₂ : State α} (triv : s₁.Trivial) : (Execution s₁ s₂) → Step.Time.RTC s₁ s₂
 | .refl => .refl
 | .trans (.time e) tl => .trans e (tl.to_timeStepRTC <| e.preserves_trivial triv)
 | .trans (.skip e) _ | .trans (.exec e) _ => absurd triv e.not_trivial

variable {s s₁ s₂ : State α}

theorem trivial_deterministic
    (triv : ¬s.Nontrivial) (e₁ : Execution s s₁) (e₂ : Execution s s₂) (ht : s₁.tag = s₂.tag) :
    s₁ = s₂ :=
  Step.Time.RTC.deterministic ht
    (e₁.to_timeStepRTC <| .of_not_nontrivial triv)
    (e₂.to_timeStepRTC <| .of_not_nontrivial triv)

theorem trivial_tag_le (triv : ¬s₁.Nontrivial) (e : Execution s₁ s₂) : s₁.tag ≤ s₂.tag :=
  e.to_timeStepRTC (.of_not_nontrivial triv) |>.tag_le

end Execution
