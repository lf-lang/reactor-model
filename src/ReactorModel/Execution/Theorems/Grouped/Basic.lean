import ReactorModel.Execution.Theorems.Grouped.Instantaneous
import ReactorModel.Execution.Theorems.Grouped.Steps
import ReactorModel.Execution.Theorems.Grouped.Tail

open ReactorType

namespace Execution

structure Grouped [Indexable α] (s₁ s₂ : State α) where
  {tl   : State α}
  steps : Grouped.Steps s₁ tl
  tail  : Grouped.Tail  tl s₂

namespace Grouped

theorem deterministic [Proper α] {s s₁ s₂ : State α} 
    (n : s.Nontrivial) (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) :
    (Grouped s s₁) → (Grouped s s₂) → s₁ = s₂
  | mk (tl := tl₁) steps₁ tail₁, mk (tl := tl₂) steps₂ tail₂ => by
    replace ht : tl₁.tag = tl₂.tag := tail₁.preserves_tag ▸ ht ▸ tail₂.preserves_tag.symm
    have hp' : tl₁.progress = tl₂.progress := by
      sorry
    replace tail₁ := steps₁.deterministic steps₂ n ht hp' ▸ tail₁
    exact tail₁.deterministic hp tail₂

end Grouped

def grouped [Indexable α] : {s₁ s₂ : State α} → (n : s₁.Nontrivial) → (s₁ ⇓ s₂) → Grouped s₁ s₂
  | _, _, _, .refl => ⟨.refl, .none⟩ 
  | _, _, n, .trans (.skip e) e' | _, _, n, .trans (.exec e) e' =>
    let ⟨steps, tail⟩ := e'.grouped $ e.preserves_nontrivial n
    match steps, tail with
    | .refl,                   .none    => ⟨.refl, .some $ .single e⟩ 
    | .refl,                   .some e' => ⟨.refl, .some $ .trans e e'⟩
    | .step (.inst ⟨f, h⟩) f', tl       => ⟨.step (.inst ⟨.trans e f, h⟩) f', tl⟩
    | .step (.time f) f',      tl       => ⟨.step (.inst ⟨.single e, f.closed⟩) $ .step f f', tl⟩
  | _, _, n, .trans (.time e) e' => 
    match e'.grouped $ e.preserves_nontrivial n with
    | ⟨.refl, tl⟩              => ⟨.step e .refl, tl⟩ 
    | ⟨.step (.inst f) f', tl⟩ => ⟨.step (.time e) $ .step f f', tl⟩
    | ⟨.step (.time f) _, _⟩   => e.nonrepeatable f n |>.elim

end Execution
