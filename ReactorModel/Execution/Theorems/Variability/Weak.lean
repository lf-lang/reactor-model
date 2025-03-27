import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.State
import ReactorModel.Execution.Theorems.Monotonicity

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
  let rcnCount := (Finite.fin s₁.rtr .rcn).toFinset.card
  let maxTimeSteps := m - s₁.tag.microstep
  -- Bound on the execution length:
  -- reaction steps, time step, ..., reaction steps, time step, reaction steps
  -- |____________ maxTimeSteps * (rcnCount + 1) _____________| + rcnCount
  exists maxTimeSteps * (rcnCount + 1) + rcnCount
  intro s₂ e ht₁ hm
  induction e generalizing m <;> simp only [length, Nat.zero_le]
  case trans s₂ s₃ e stp ih =>
    change e.length < maxTimeSteps * (rcnCount + 1) + rcnCount
    -- 1. We can somewhat easily establish s₁.time = s₂.time = s₃.time
    have ht₂ : s₂.tag.time = t := sorry
    have ht₃ : s₃.tag.time = t := sorry
    have hm₃ : s₃.tag.microstep ≤ m := sorry -- by hm and ht₃
    -- Depending on whether the final step is a time or a reaction step, we get different values
    -- for `s₂.tag.microstep`.
    cases stp
    case time stp =>
      have hm₂ : s₂.tag.microstep < s₃.tag.microstep := sorry -- by stp.tag_lt and ht₂, ht₃
      have hm₂' := lt_of_lt_of_le hm₂ hm₃
      specialize ih (m - 1) sorry -- by hm₂'
      simp only [maxTimeSteps]
      cases m
      case zero => contradiction
      case succ m =>
        have hm₁ : s₁.tag.microstep < m := sorry -- by hm₂ and e
        simp_all only [Nat.add_one_sub_one, gt_iff_lt]
        suffices h : (m - s₁.tag.microstep) * (rcnCount + 1) + rcnCount < (m + 1 - s₁.tag.microstep) * (rcnCount + 1) + rcnCount by omega
        simp_all only [Nat.add_lt_add_iff_right, Nat.zero_lt_succ, Nat.mul_lt_mul_right]
        omega
    -- TODO: These two cases should be analogous.
    case skip stp =>
      have hm₂ : s₂.tag.microstep = s₃.tag.microstep := by rw [stp.preserves_tag]
      have hm₂' := hm₂ ▸ hm₃
      specialize ih m sorry -- by hm₂'
      simp [maxTimeSteps]
      sorry -- PROBLEM: For this approach to work we'd need something like strong induction on
            --          execution traces, so it's probably easier to take the grouped execution
            --          approach instead.
    case exec => sorry

    -- 2. The number of time-steps taken from s₁ to s₃ is bounded by m - s₁.tag.microstep.
    --    Thus, the length of e is also bounded by m - s₁.tag.microstep.
    --    The number of steps that can be taken in an execution which takes at most N time steps
    --    is bounded by N * (#rcns + 1) + #rcns.
    --    TODO: Does our grouping theorem help with this?
