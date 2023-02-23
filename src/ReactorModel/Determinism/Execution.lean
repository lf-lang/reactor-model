import ReactorModel.Determinism.ExecutionStep

open Classical 

namespace Execution

-- This is only used for the proof of `trivial_deterministic`.
inductive AdvanceTag.RTC : State → State → Type
  | refl : RTC s s
  | trans : (s₁ ⇓- s₂) → (RTC s₂ s₃) → RTC s₁ s₃   

-- This is only used for the proof of `trivial_deterministic`.
theorem AdvanceTag.RTC.deterministic 
  (a₁ : AdvanceTag.RTC s s₁) (a₂ : AdvanceTag.RTC s s₂) (ht : s₁.tag = s₂.tag) : s₁ = s₂ := by
  induction a₁ <;> cases a₂
  case refl.refl                       => rfl
  case' refl.trans a _, trans.refl _ a => exact absurd ht a.tag_ne
  case trans.trans a₁ _ hi _ a₂ c₂     => exact hi (a₂.determinisic a₁ ▸ c₂) ht

-- This is only used for the proof of `trivial_deterministic`.
def trivial_erase_exec_steps [State.Trivial s₁] : (s₁ ⇓* s₂) → AdvanceTag.RTC s₁ s₂
  | refl => .refl
  | step (.advance a) e' => 
    have := a.preserves_Trivial -- TODO: Make this work via type class inference.
    .trans a e'.trivial_erase_exec_steps
  | step (.close e) e' => 
    have := e.preserves_Trivial -- TODO: Make this work via type class inference.
    e.trivial_eq ▸ e'.trivial_erase_exec_steps

theorem trivial_deterministic [trivial : State.Trivial s] 
    (e₁ : s ⇓* s₁) (e₂ : s ⇓* s₂) (ht : s₁.tag = s₂.tag) : s₁ = s₂ :=
  AdvanceTag.RTC.deterministic e₁.trivial_erase_exec_steps e₂.trivial_erase_exec_steps ht

theorem tag_le : (s₁ ⇓* s₂) → s₁.tag ≤ s₂.tag
  | refl      => le_refl _
  | step e e' => le_trans e.tag_le e'.tag_le

theorem seq_progress_ssubset_or_tag_lt [State.Nontrivial s₁] : 
    (s₁ ⇓ s₂) → (s₂ ⇓* s₃) → (s₁.progress ⊂ s₃.progress) ∨ (s₁.tag < s₃.tag)
  | e₁₂,        .step e e' => .inr $ lt_of_lt_of_le (e₁₂.seq_tag_lt e) e'.tag_le
  | .close e,   .refl      => .inl $ e.progress_ssubset
  | .advance a, .refl      => .inr $ a.tag_lt

theorem nontrivial_deterministic [State.Nontrivial s] :
    (s ⇓* s₁) → (s ⇓* s₂) → (s₁.tag = s₂.tag) → (s₁.progress = s₂.progress) → s₁ = s₂
  | refl, refl, _, _ => rfl
  | step e₁ e₁', step e₂ e₂', ht, hp => 
    have := e₂.preserves_Nontrivial -- TODO: Make this work via type class inference.
    nontrivial_deterministic (e₁.deterministic e₂ ▸ e₁') e₂' ht hp
  | refl, step e e', ht, hp | step e e', refl, ht, hp => 
    match seq_progress_ssubset_or_tag_lt e e' with
    | .inl h => absurd hp $ Finset.ssubset_ne (by simp_all) 
    | .inr h => absurd ht $ ne_of_lt h

theorem deterministic : 
    (s ⇓* s₁) → (s ⇓* s₂) → (s₁.tag = s₂.tag) → (s₁.progress = s₂.progress) → s₁ = s₂ := 
  if h : State.Nontrivial s 
  then nontrivial_deterministic
  else fun e₁ e₂ ht _ => trivial_deterministic e₁ e₂ ht (trivial := .of_not_Nontrivial h)
  
end Execution