import ReactorModel.Objects.Reactor.Basic

namespace ReactorType

-- The relation expresses that `rtr₁` is nested in `rtr₂`.
def Nested [ReactorType α] (rtr₁ rtr₂ : α) : Prop :=
  ∃ i, rtr₂{.rtr}{i} = some rtr₁

class WellFounded (α) extends ReactorType α where
  wf : WellFounded $ Nested (α := α)

variable [ReactorType.WellFounded α]

theorem WellFounded.induction {motive : α → Prop} 
    (nest : ∀ rtr, (∀ n, (∃ i, rtr{.rtr}{i} = some n) → motive n) → motive rtr) : 
    ∀ rtr, motive rtr := 
  (wf.induction · nest)

namespace ReactorType