import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.Grouped.Instantaneous
import ReactorModel.Execution.Theorems.Grouped.Steps
import ReactorModel.Execution.Theorems.Grouped.Tail

open Reactor

namespace Execution

structure Grouped [Hierarchical α] (s₁ s₂ : State α) where
  {tl   : State α}
  steps : Grouped.Steps s₁ tl
  tail  : Grouped.Tail  tl s₂

namespace Grouped

def length [Hierarchical α] {s₁ s₂ : State α} (e : Grouped s₁ s₂) : Nat :=
  e.steps.length + e.tail.length

-- TODO: Most of the case bashing is copied from `Steps.deterministic`. What is the underlying lemma?
theorem deterministic
    [Proper α] {s s₁ s₂ : State α} (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) :
    (Grouped s s₁) → (Grouped s s₂) → s₁ = s₂
  | mk (tl := tl₁) steps₁ tail₁, mk (tl := tl₂) steps₂ tail₂ => by
    replace ht : tl₁.tag = tl₂.tag := tail₁.preserves_tag ▸ ht ▸ tail₂.preserves_tag.symm
    induction steps₁ <;> cases steps₂
    case refl.refl => exact tail₁.deterministic hp tail₂
    case step.step e₁ _ hi _ e₂ e₂' =>
      cases e₁.deterministic e₂
      exact hi tail₁ e₂' ht
    all_goals cases ‹Step _ _›
    case refl.step.time e' e   => exact absurd ht <| ne_of_lt <| lt_of_lt_of_le e.tag_lt e'.tag_le
    case step.refl.time e' _ e => exact absurd ht.symm <| ne_of_lt <| lt_of_lt_of_le e.tag_lt e'.tag_le
    all_goals cases ‹Steps _ _›
    case refl.step.inst.refl e =>
      cases tail₂.closed_to_none e.closed
      cases tail₁
      case none   => exact absurd hp <| ne_of_ssubset e.progress_ssubset
      case some f => exact f.deterministic e.exec hp
    case step.refl.inst.refl e _  =>
      cases tail₁.closed_to_none e.closed
      cases tail₂
      case none   => exact absurd hp.symm <| ne_of_ssubset e.progress_ssubset
      case some f => exact e.exec.deterministic f hp
    all_goals cases ‹Step _ _›
    case refl.step.inst.step.time e _ f' f => exact absurd ht <| ne_of_lt <| e.preserves_tag ▸ lt_of_lt_of_le f.tag_lt f'.tag_le
    case step.refl.inst.step.time e _ f' f => exact absurd ht.symm <| ne_of_lt <| e.preserves_tag ▸ lt_of_lt_of_le f.tag_lt f'.tag_le
    case refl.step.inst.step.inst e _ f' f => exact e.nonrepeatable f |>.elim
    case step.refl.inst.step.inst e _ f' f => exact e.nonrepeatable f |>.elim

theorem tag_le [Hierarchical α] {s₁ s₂ : State α} (e : Grouped s₁ s₂) : s₁.tag ≤ s₂.tag :=
  e.tail.preserves_tag ▸ e.steps.tag_le

end Grouped

def toGrouped [Hierarchical α] {s₁ s₂ : State α} : (Execution s₁ s₂) → Grouped s₁ s₂
  | .refl => ⟨.refl, .none⟩
  | .trans stp tl =>
    match tl.toGrouped with
    | ⟨.refl, tl⟩ =>
      match stp with
      | .time e => ⟨.step e .refl, tl⟩
      | .skip e | .exec e =>
        match tl with
        | .none    => ⟨.refl, .some <| .single e⟩
        | .some e' => ⟨.refl, .some <| .trans e e'⟩
    | ⟨.step (.inst f) f', tl⟩ =>
      match stp with
      | .time e           => ⟨.step (.time e) <| .step f f', tl⟩
      | .skip e | .exec e => ⟨.step (.inst ⟨.trans e f.exec, f.closed⟩) f', tl⟩
    | ⟨.step (.time f) f', tl⟩ =>
      match stp with
      | .time e           => ⟨.step (.time e) (.step (.time f) f'), tl⟩
      | .skip e | .exec e => ⟨.step (.inst ⟨.single e, f.closed⟩) <| .step f f', tl⟩

theorem toGrouped_length [Hierarchical α] {s₁ s₂ : State α} (e : Execution s₁ s₂) :
    e.length = e.toGrouped.length := by
  induction e using toGrouped.induct
  all_goals
    simp only [length, toGrouped, *]
    simp +arith [Grouped.length, Grouped.Steps.length, Grouped.Step.length, Grouped.Tail.length,
                 Instantaneous.Closed.length, Instantaneous.Step.TC.length]

  end Execution
