import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.State
import ReactorModel.Execution.Theorems.Variability.LoopModel

open Classical Reactor

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
    (s'.tag < g) → e.length < b

-- Properness of a finite reactor model is not sufficient for finite variability. This is a
-- consequence of logical tags being super-dense.
--
-- Proof Idea: Construct a reactor with a reaction which always schedules and action for the
--             current logical time. This only ever increases the micro-step, but not the time.
theorem not_finitely_variable : ¬∀ (α) [Proper α] [Reactor.Finite α], FiniteVariability α := by
  intro h
  let s₁ : State LoopModel.Rtr := {
    rtr := { act := true },
    tag := ⟨0, 0⟩,
    progress := ∅,
    events
      | .r => none
      | .a => some <| .singleton ⟨0, 0⟩ true
  }
  have ⟨b, h⟩ := h _ ⟨1, 0⟩ s₁
  let s₂ : State LoopModel.Rtr := {
    rtr := { act := true },
    tag := ⟨0, b⟩,
    progress := ∅,
    events
      | .r => none
      | .a => sorry -- TODO: The execution semantics don't include deleting old events.
  }
  let e : Execution s₁ s₂ := sorry -- TODO: Construct this recursively.
  have hl : e.length = b := sorry
  exact lt_irrefl b (hl ▸ h e Time.Tag.lt_of_lt_time)
