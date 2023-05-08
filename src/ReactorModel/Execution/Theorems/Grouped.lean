import ReactorModel.Execution.Trace
import ReactorModel.Execution.Theorems.Grouped.Instantaneous
import ReactorModel.Execution.Theorems.Grouped.Head
import ReactorModel.Execution.Theorems.Grouped.Steps
import ReactorModel.Execution.Theorems.Grouped.Tail
import ReactorModel.Execution.Theorems.Nontrivial

open ReactorType

namespace Execution

structure Grouped [Indexable α] (s₁ s₂ : State α) where
  hd    : State α
  tl    : State α
  head  : Grouped.Head  s₁ hd
  steps : Grouped.Steps hd tl
  tail  : Grouped.Tail  tl s₂

-- TODO: You can add a condition of nontriviality if you want.
--       In fact, the theorems in Nontrivial.lean are probably the right ones to solve this.
theorem Grouped.deterministic 
    [Proper α] {s s₁ s₂ : State α} (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) :
    (Grouped s s₁) → (Grouped s s₂) → s₁ = s₂ := by
  intro ⟨hd₁, tl₁, head₁, steps₁, tail₁⟩ ⟨hd₂, tl₂, head₂, steps₂, tail₂⟩
  /-replace ht : tl₁.tag = tl₂.tag := tail₁.preserves_tag ▸ tail₂.preserves_tag ▸ ht
  suffices h : hd₁ = hd₂ by
    subst h
    cases steps₁.deterministic steps₂ ht
    cases tail₁.deterministic tail₂ hp
    rfl
  -/
  sorry 

-- TODO: Move this theorem into the Nontrivial.lean file?
def grouped [Indexable α] : {s₁ s₂ : State α} → (n : s₁.Nontrivial) → (s₁ ⇓ s₂) → Grouped s₁ s₂
  | s, _, _, .refl => 
    ⟨s, s, .nil, .refl, .nil⟩ 
  | s₁, s₃, n, .trans (.skip e) e' (s₂ := s₂) => 
    let ⟨hd, tl, head, steps, tail⟩ := e'.grouped $ e.preserves_nontrivial n
    match hh : head, hs : steps, ht : tail with
    | .nil,    .refl,    .nil    => sorry -- contradiction by e
    | .nil,    .refl,    .time _ => sorry -- ⟨s₁, s₁, .nil, .refl, .inst $ .trans (.skip e) f⟩
    | .nil,    .step .., .nil    => sorry
    | .nil,    .step .., .time _ => sorry
    | .inst _, .refl,    .nil    => sorry
    | .inst _, .refl,    .time _ => sorry
    | .inst _, .step .., .nil    => sorry
    | .inst _, .step .., .time _ => sorry
  | s₁, s₂, _, .trans (.exec e) e' => sorry -- this should be identical to the one above
  | s₁, s₃, n, .trans (.time e) e' (s₂ := s₂) => 
    let g := e'.grouped $ e.preserves_nontrivial n
    sorry
    -- match h : g.head with
    -- | .nil    => { g with head := .time $ (symm ‹_› : s₂ = g.hd) ▸ e }
    -- | .time f => e.nonrepeatable f n |>.elim

end Execution
