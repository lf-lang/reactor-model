import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.State
import ReactorModel.Execution.Theorems.Grouped.Basic
import ReactorModel.Objects.Reactor.Theorems.Finite

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
    (s.tag.time = t) → (s'.tag ≤ ⟨t, m⟩) → e.length ≤ b

theorem weakly_finitely_variable [Proper α] [fin : Reactor.Finite α] : WeakFiniteVariability α := by
  intros t m s₁
  exists (m - s₁.tag.microstep) * (s₁.rtr#.rcn + 1) + (s₁.rtr#.rcn + 1)
  intro s₂ e ht₁ hm
  let g := e.toGrouped
  rw [e.toGrouped_length, Grouped.length]
  apply Nat.add_le_add ?_ (equiv_card_eq g.steps.equiv _ ▸ g.tail.length_le)
  suffices h : g.steps.steps = m - s₁.tag.microstep by exact h ▸ g.steps.length_le
  sorry
