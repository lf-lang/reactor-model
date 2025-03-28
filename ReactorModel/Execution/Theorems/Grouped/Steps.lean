import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.Grouped.Instantaneous
import ReactorModel.Objects.Reactor.Theorems.Hierarchical

open Reactor

namespace Execution.Grouped

inductive Step [Hierarchical α] (s₁ s₂ : State α)
  | inst : (s₁ ↓ᵢ| s₂) → Step s₁ s₂
  | time : (s₁ ↓ₜ s₂) → Step s₁ s₂

namespace Step

variable [Hierarchical α] {s₁ s₂ : State α}

instance : Coe (s₁ ↓ᵢ| s₂) (Step s₁ s₂) where
  coe := inst

instance : Coe (s₁ ↓ₜ s₂) (Step s₁ s₂) where
  coe := time

def length : (Step s₁ s₂) → Nat
  | inst e => e.length
  | time _ => 1

def length_le [Reactor.Finite α] {s₁ s₂ : State α} :
    (e : Step s₁ s₂) → e.length ≤ s₁.rtr#.rcn + 1
  | inst e => e.length_le_rcns_card.trans (Nat.le_succ _)
  | time _ => by simp [length]

theorem tag_le : (Step s₁ s₂) → s₁.tag ≤ s₂.tag
  | inst e => e.preserves_tag ▸ le_refl _
  | time e => le_of_lt e.tag_lt

theorem equiv : (Step s₁ s₂) → s₁.rtr ≈ s₂.rtr
  | inst e | time e => e.equiv

theorem preserves_nontrivial (n : s₁.Nontrivial) : (Step s₁ s₂) → s₂.Nontrivial
  | inst e | time e => e.preserves_nontrivial n

end Step

theorem Step.deterministic [Proper α] {s s₁ s₂ : State α} : (Step s s₁) → (Step s s₂) → s₁ = s₂
  | inst e₁, inst e₂                    => e₁.deterministic e₂
  | time e₁, time e₂                    => e₁.deterministic e₂
  | inst e₁, time e₂ | time e₂, inst e₁ => e₁.not_closed e₂.closed |>.elim

inductive Steps [Hierarchical α] : State α → State α → Type
  | refl : Steps s s
  | step : (Step s₁ s₂) → (Steps s₂ s₃) → Steps s₁ s₃

namespace Steps

section

variable [Hierarchical α]

def length {s₁ s₂ : State α} : (Steps s₁ s₂) → Nat
  | refl      => 0
  | step e e' => e'.length + e.length

def steps {s₁ s₂ : State α} : (Steps s₁ s₂) → Nat
  | refl      => 0
  | step _ e' => e'.steps + 1

theorem equiv {s₁ s₂ : State α} : (Steps s₁ s₂) → s₁.rtr ≈ s₂.rtr
  | refl      => .refl _
  | step e e' => Equivalent.trans e.equiv e'.equiv

def length_le [Reactor.Finite α] {s₁ s₂ : State α} (e : Steps s₁ s₂) :
    e.length ≤ e.steps * (s₁.rtr#.rcn + 1) := by
  induction e <;> simp only [length, Nat.zero_le]
  case step stp e ih =>
    apply le_trans <| Nat.add_le_add ih stp.length_le
    simp [steps, equiv_card_eq stp.equiv, Nat.add_mul]

theorem tag_le {s₁ s₂ : State α} : (Steps s₁ s₂) → s₁.tag ≤ s₂.tag
  | .refl      => le_rfl
  | .step e e' => e.tag_le.trans e'.tag_le

end

theorem deterministic [Proper α] {s s₁ s₂ : State α}
    (e₁ : Steps s s₁) (e₂ : Steps s s₂) (n : s.Nontrivial) (ht : s₁.tag = s₂.tag)
    (hp : s₁.progress = s₂.progress) : s₁ = s₂ := by
  induction e₁ <;> cases e₂
  case refl.refl => rfl
  case step.step e₁ _ hi _ e₂ e₂' =>
    exact hi (e₁.deterministic e₂ ▸ e₂') (e₁.preserves_nontrivial n) ht hp
  all_goals cases ‹Step _ _›
  case refl.step.time e' e   => exact absurd ht <| ne_of_lt <| lt_of_lt_of_le e.tag_lt e'.tag_le
  case step.refl.time e' _ e => exact absurd ht.symm <| ne_of_lt <| lt_of_lt_of_le e.tag_lt e'.tag_le
  all_goals cases ‹Steps _ _›
  case refl.step.inst.refl e' e => exact absurd hp <| ne_of_ssubset e.progress_ssubset
  case step.refl.inst.refl e _  => exact absurd hp.symm <| ne_of_ssubset e.progress_ssubset
  all_goals cases ‹Step _ _›
  case refl.step.inst.step.time e _ f' f => exact absurd ht <| ne_of_lt <| e.preserves_tag ▸ lt_of_lt_of_le f.tag_lt f'.tag_le
  case step.refl.inst.step.time e _ f' f => exact absurd ht.symm <| ne_of_lt <| e.preserves_tag ▸ lt_of_lt_of_le f.tag_lt f'.tag_le
  case refl.step.inst.step.inst e _ f' f => exact e.nonrepeatable f |>.elim
  case step.refl.inst.step.inst e _ f' f => exact e.nonrepeatable f |>.elim

end Execution.Grouped.Steps
