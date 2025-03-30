import ReactorModel.Execution.Theorems.Variability.Loop.Execution

open Reactor

namespace Execution

-- Property (2) on page 10 of https://www.informatik.uni-bremen.de/agbs/jp/papers/trs_script.pdf.
-- "The computation can perform only finitely many state changes in any finite time interval."
--
-- We formalize this as:
-- For any initial execution state `s₁` and tag `g`, there exists a bound `b` on the length of
-- executions which start at `s₁` and stay below `g`.
--
-- It is important that the bound `b` can depend on `s₁`, because otherwise it may be exeeded simply
-- by the sheer number of reactions contained in the reactor of `s₁`, or by the number of events
-- already present in its event queue.
--
-- Note: This property is parameterized over the reactor type (`α`), because finite variability is a
--       property of the *model* of Reactors, and the given reactor type (or rather its accompanying
--       type class instances) defines the model.
def FiniteVariability (α) [Hierarchical α] : Prop :=
  ∀ g s, ∃ b, ∀ {s' : State α} (e : Execution s s'),
    (s'.tag ≤ g) → e.length ≤ b

-- Properness of a finite reactor model is not sufficient for finite variability. This is a
-- consequence of logical tags being super-dense.
--
-- Proof Idea: Construct a reactor with a reaction which always schedules an action for the current
--             logical time. This only ever increases the microstep, but not the time.
theorem not_finitely_variable : ¬∀ (α) [Proper α] [Reactor.Finite α], FiniteVariability α := by
  intro h
  have ⟨b, h⟩ := h _ ⟨1, 0⟩ (Loop.state₀ 0)
  have := h (Loop.execution₀ <| b + 1) (le_of_lt <| Time.Tag.lt_of_lt_time Nat.zero_lt_one)
  have := Loop.execution₀_length_le (b + 1)
  omega
