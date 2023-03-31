import ReactorModel.Objects.Reactor.Basic

namespace ReactorType

-- The relation expresses that `rtr₁` is nested in `rtr₂`.
abbrev Nested [ReactorType α] (rtr₁ rtr₂ : α) : Prop :=
  ∃ i, nest rtr₂ i = some rtr₁

protected class WellFounded (α) extends Extensional α where
  wf : WellFounded $ Nested (α := α)

theorem WellFounded.induction [ReactorType.WellFounded α] {motive : α → Prop} 
    (nest : ∀ rtr, (∀ n, (∃ i, nest rtr i = some n) → motive n) → motive rtr) : ∀ rtr, motive rtr := 
  (wf.induction · nest)

namespace ReactorType