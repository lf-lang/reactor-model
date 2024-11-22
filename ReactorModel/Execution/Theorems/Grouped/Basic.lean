import ReactorModel.Execution.Theorems.Grouped.Instantaneous
import ReactorModel.Execution.Theorems.Grouped.Steps
import ReactorModel.Execution.Theorems.Grouped.Tail

open Reactor

namespace Execution

structure Grouped [Hierarchical α] (s₁ s₂ : State α) where
  {tl   : State α}
  steps : Grouped.Steps s₁ tl
  tail  : Grouped.Tail  tl s₂

-- TODO: Most of the case bashing is copied from `Steps.deterministic`. What is the underlying lemma?
theorem Grouped.deterministic [Proper α] {s s₁ s₂ : State α}
    (n : s.Nontrivial) (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) :
    (Grouped s s₁) → (Grouped s s₂) → s₁ = s₂
  | mk (tl := tl₁) steps₁ tail₁, mk (tl := tl₂) steps₂ tail₂ => by
    replace ht : tl₁.tag = tl₂.tag := tail₁.preserves_tag ▸ ht ▸ tail₂.preserves_tag.symm
    induction steps₁ <;> cases steps₂
    case refl.refl => exact tail₁.deterministic hp tail₂
    case step.step e₁ _ hi _ e₂ e₂' =>
      cases e₁.deterministic e₂
      exact hi (e₁.preserves_nontrivial n) tail₁ e₂' ht
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

theorem to_grouped [Hierarchical α] {s₁ s₂ : State α} (n : s₁.Nontrivial) (e : s₁ ⇓ s₂) :
    Nonempty (Grouped s₁ s₂) := by
  induction e <;> try cases ‹_ ↓ _›
  case refl => exact ⟨.refl, .none⟩
  case trans.time hi e =>
    exact match hi <| e.preserves_nontrivial n with
    | ⟨.refl, tl⟩              => ⟨.step e .refl, tl⟩
    | ⟨.step (.inst f) f', tl⟩ => ⟨.step (.time e) <| .step f f', tl⟩
    | ⟨.step (.time f) _, _⟩   => e.nonrepeatable f n |>.elim
  all_goals
    case _ hi e =>
      let ⟨steps, tail⟩ := hi <| e.preserves_nontrivial n
      exact match steps, tail with
      | .refl,                   .none    => ⟨.refl, .some <| .single e⟩
      | .refl,                   .some e' => ⟨.refl, .some <| .trans e e'⟩
      | .step (.inst ⟨f, h⟩) f', tl       => ⟨.step (.inst ⟨.trans e f, h⟩) f', tl⟩
      | .step (.time f) f',      tl       => ⟨.step (.inst ⟨.single e, f.closed⟩) <| .step f f', tl⟩

end Execution
