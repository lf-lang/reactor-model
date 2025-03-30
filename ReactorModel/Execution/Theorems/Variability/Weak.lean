import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.State
import ReactorModel.Execution.Theorems.Grouped.Basic
import ReactorModel.Objects.Reactor.Theorems.Finite

open Reactor Time.Tag

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

theorem weakly_finitely_variable [Hierarchical α] [Reactor.Finite α] : WeakFiniteVariability α := by
  intros t m s₁
  exists (2 * (m - s₁.tag.microstep) + 1) * (s₁.rtr#.rcn + 1) + (s₁.rtr#.rcn + 1)
  intro s₂ e ht hm
  let g := e.toGrouped
  rw [e.toGrouped_length, Grouped.length]
  apply Nat.add_le_add ?_ (equiv_card_eq g.steps.equiv _ ▸ g.tail.length_le)
  apply le_trans g.steps.length_le
  have htl := g.tail.preserves_tag
  have h := le_antisymm (le_to_le_time g.steps.tag_le) <| ht ▸ le_to_le_time (htl.symm ▸ hm)
  apply le_trans <| Nat.mul_le_mul_right (s₁.rtr#Component.rcn + 1) (g.steps.count_le h)
  have h := htl ▸ le_microsteps_of_eq_time (ht ▸ hm) (htl ▸ h.symm)
  apply Nat.mul_le_mul_right
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  apply Nat.sub_le_sub_right h
