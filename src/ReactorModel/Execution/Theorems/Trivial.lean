import ReactorModel.Execution.Theorems.Nontrivial
import ReactorModel.Execution.Theorems.SkipStep
import ReactorModel.Execution.Theorems.ExecStep

open ReactorType Classical

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

inductive RTC : State α → State α → Prop
  | refl : RTC s s
  | trans : (s₁ ↓ₜ s₂) → (RTC s₂ s₃) → RTC s₁ s₃   

theorem RTC.tag_le {s₁ s₂ : State α} (e : RTC s₁ s₂) : s₁.tag ≤ s₂.tag := by
  induction e with
  | refl         => exact le_refl _
  | trans a _ hi => exact le_trans (le_of_lt a.tag_lt) hi

theorem RTC.deterministic {s s₁ s₂ : State α} 
    (ht : s₁.tag = s₂.tag) (e₁ : RTC s s₁) (e₂ : RTC s s₂) : s₁ = s₂ := by
  induction e₁ generalizing s₂ <;> cases e₂
  case refl.refl         => rfl
  case refl.trans e e'   => exact absurd ht      (ne_of_lt $ lt_of_lt_of_le e.tag_lt e'.tag_le)
  case trans.refl e e' _ => exact absurd ht.symm (ne_of_lt $ lt_of_lt_of_le e.tag_lt e'.tag_le)
  case trans.trans e₁ e₁' hi _ e₂ e₂' => exact hi ht (e₂.deterministic e₁ ▸ e₂')
  
end Step.Time

variable {s s₁ s₂ : State α} 

theorem to_timeStepRTC (triv : s₁.Trivial) (e : s₁ ⇓ s₂) : Step.Time.RTC s₁ s₂ := by
  induction e <;> try cases ‹_ ↓ _›
  case refl            => exact .refl  
  case trans.skip e    => exact absurd triv e.not_trivial
  case trans.exec e    => exact absurd triv e.not_trivial
  case trans.time hi e => exact .trans e (hi $ e.preserves_trivial triv)

theorem trivial_deterministic 
    (triv : ¬s.Nontrivial) (e₁ : s ⇓ s₁) (e₂ : s ⇓ s₂) (ht : s₁.tag = s₂.tag) : s₁ = s₂ :=
  Step.Time.RTC.deterministic ht
    (e₁.to_timeStepRTC $ .of_not_nontrivial triv) 
    (e₂.to_timeStepRTC $ .of_not_nontrivial triv) 

end Execution