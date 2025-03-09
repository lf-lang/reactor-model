import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.State

open Classical Reactor

namespace Execution

-- "Weak finite variability" restricts the notion of finite variability to a single logical time.
-- That is, this property holds if for any given logical time `t`, there exists a bound on the
-- length of execution traces which occur at tags `g` with time `g.time = t`. Stated differently,
-- this means that you can't have infinitely many state changes between two microsteps of the same
-- logical time.
--
-- TODO: This gives me ε/δ vibes. Does this alternation of ∃ and ∀ correspond to some existing
--       notion like limits or convergence?
def WeakFiniteVariability (α) [Hierarchical α] : Prop :=
  ∀ t m s, ∃ b, ∀ {s' : State α} (e : Execution s s'),
    (s.tag.time = t) → (s'.tag < ⟨t, m⟩) → e.length < b

theorem weakly_finitely_variable [Proper α] [Reactor.Finite α] : WeakFiniteVariability α := by
  sorry
