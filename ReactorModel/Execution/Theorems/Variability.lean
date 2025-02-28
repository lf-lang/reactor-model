import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.State

open Classical Reactor

namespace Execution

def length [Hierarchical α] {s₁ s₂ : State α} : (s₁ ⇓ s₂) → Nat
  | .refl      => 0
  | .trans _ e => e.length + 1

-- Property (2) on page 10 of https://www.informatik.uni-bremen.de/agbs/jp/papers/trs_script.pdf.
-- "The computation can perform only finitely many state changes in any finite time interval."
--
-- We formalize this as:
-- For any tag `g`, there exists a bound on the length of execution traces which do not exceed `g`.
--
-- Note: This property is parameterized over the reactor type (`α`), because finite variability is a
--       property of the *model* of Reactors, and the given reactor type (or rather its accompanying
--       type class instances) defines the model.
def FiniteVariability (α) [Hierarchical α] : Prop :=
  ∀ g, ∃ b, ∀ {s₁ s₂ : State α} (e : s₁ ⇓ s₂), (s₂.tag < g) → e.length < b

-- Proper reactors do not satisfy finite variability as logical tags are super-dense.
theorem not_finitely_variable [Proper α] : ¬(FiniteVariability α) := by
  -- Proof Idea: Construct a reactor with a reaction action which always schedules and action for
  --             the current logical time. This will only ever increase the micro-step, but not the
  --             time, so for tags with `g.time > 0`, there does not exist a bound `b`.
  sorry

-- "Weak finite variability" restricts the notion of finite variability to a single logical time.
-- That is, this property holds if for any given logical time `t`, there exists a bound on the
-- length of execution traces which occur at tags `g` with time `g.time = t`. Stated differently,
-- this means that you can't have infinitely many state changes between two microsteps of the same
-- logical time.
--
-- TODO: This gives me ε/δ vibes. Does this alternation of ∃ and ∀ correspond to some existing
--       notion like limits or convergence?
def WeakFiniteVariability (α) [Hierarchical α] : Prop :=
  ∀ t m, ∃ b, ∀ {s₁ s₂ : State α} (e : s₁ ⇓ s₂), (s₁.tag.time = t) → (s₂.tag < ⟨t, m⟩) → e.length < b

theorem weakly_finitely_variable [Proper α] : WeakFiniteVariability α := by
  sorry
