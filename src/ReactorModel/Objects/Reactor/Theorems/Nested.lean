import ReactorModel.Objects.Reactor.Theorems.Indexable
import ReactorModel.Objects.Reactor.Wellformed

namespace ReactorType

open Indexable
variable [Indexable α] [Indexable β] {rtr rtr₁ : α}

namespace Dependency

theorem nested (h : nest rtr₁ i = some rtr₂) (d : i₁ <[rtr₂] i₂) : i₁ <[rtr₁] i₂ := by
  induction d with
  | prio h₁          => exact prio (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | mutNorm h₁       => exact mutNorm (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | depOverlap h₁ h₂ => exact depOverlap (obj?_nested h h₁) (obj?_nested h h₂) ‹_› ‹_› ‹_›
  | mutNest h₁       => exact mutNest (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | trans _ _ d₁ d₂  => exact trans d₁ d₂

theorem Acyclic.nested (a : Acyclic rtr₁) (h : nest rtr₁ i = some rtr₂) : Acyclic rtr₂ :=
  fun i d => absurd (d.nested h) (a i)

end Dependency

namespace Wellformed

set_option hygiene false in
scoped macro "wf_nested_proof " name:ident : term => `(
  @fun
  | (_ : ID) => ($name ‹_› $ obj?_nested h ·)
  | ⊤        => ($name ‹_› <| obj?_nested_root h · |>.choose_spec)
)

theorem nested (wf : Wellformed rtr₁) (h : nest rtr₁ i = some rtr₂) : Wellformed rtr₂ where
  overlap_prio        := wf_nested_proof overlap_prio
  hazards_prio        := wf_nested_proof hazards_prio
  mutation_prio       := wf_nested_proof mutation_prio
  valid_deps          := wf_nested_proof valid_deps
  acyclic_deps        := wf.acyclic_deps.nested h
  unique_inputs h₁ h₂ := wf.unique_inputs (obj?_nested h h₁) (obj?_nested h h₂)

end Wellformed
end ReactorType