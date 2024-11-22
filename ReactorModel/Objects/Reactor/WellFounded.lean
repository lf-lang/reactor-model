import ReactorModel.Objects.Reactor.Basic

namespace Reactor

-- The relation expresses that `rtr₁` is nested in `rtr₂`.
def Nested [Reactor α] (rtr₁ rtr₂ : α) : Prop :=
  ∃ i, rtr₂{.rtr}{i} = some rtr₁

class WellFounded (α) extends Reactor α where
  wf : _root_.WellFounded <| Nested (α := α)

variable [WellFounded α]

theorem WellFounded.induction {motive : α → Prop}
    (nested : ∀ rtr, (∀ n, (∃ i, rtr{.rtr}{i} = some n) → motive n) → motive rtr) :
    ∀ rtr, motive rtr :=
  (wf.induction · nested)

namespace Reactor
