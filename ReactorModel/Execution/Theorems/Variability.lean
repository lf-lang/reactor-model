import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.State

open Classical Reactor

namespace Execution

def length [Hierarchical α] {s₁ s₂ : State α} : (Execution s₁ s₂) → Nat
  | .refl      => 0
  | .trans _ e => e.length + 1

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

-- Properness of a reactor model is not sufficient for finite variability. This is a conequence of
-- logical tags being super-dense.
--
-- Proof Idea: Construct a reactor with a reaction which always schedules and action for the
--             current logical time. This only ever increases the micro-step, but not the time.
theorem not_finitely_variable : ¬∀ (α) [Proper α], FiniteVariability α := by
  intro h
  -- TODO: Construct a simple proper reactor model `R`. This is probably non-trivial.
  let R : Type := sorry
  letI : Proper R := sorry
  let s : State R := { rtr := sorry, tag := ⟨0, 0⟩, progress := ∅, events := ∅ } -- TODO: Add an initial event.
  have ⟨b, h⟩ := h R ⟨1, 0⟩ s
  let s' : State R := { rtr := sorry, tag := ⟨0, b⟩, progress := sorry, events := sorry }
  let e : Execution s s' := sorry
  have hl : e.length = b := sorry
  exact lt_irrefl b (hl ▸ h e Time.Tag.lt_of_lt_time)

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

theorem weakly_finitely_variable [Proper α] : WeakFiniteVariability α := by
  sorry
