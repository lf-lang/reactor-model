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

private def LoopModel.state₀ (microstep : Nat) : State LoopModel.Rtr where
  rtr := { act := true }
  tag := ⟨0, microstep⟩
  progress := ∅
  events
    | .r => none
    | .a => actionEvents microstep
where
  actionEvents : Nat → Time.Tag ⇉ Bool
    | 0 => .singleton ⟨0, 0⟩ true
    | n + 1 => sorry -- TODO: The execution semantics don't include deleting old events.

private def LoopModel.execution₀ : (microstep : Nat) → Execution (state₀ 0) (state₀ microstep)
  | 0     => .refl
  | m + 1 =>
    let e := execution₀ m
    let s₁ := state₀ m
    let s₂ := s₁.record .r
    let s₃ := state₀ (m + 1)
    have hs : { s₂ with tag := ⟨0, m + 1⟩ } = s₃ := sorry
    let timeStep : s₂ ↓ₜ s₃ := hs ▸ sorry -- .Step.Time.mk sorry sorry sorry
    .trans (.trans (execution₀ m) (.exec <| execStep m)) (.time timeStep)
where
  execStep (m) : (state₀ m) ↓ₑ (state₀ m |>.record .r) :=
    .mk
      {
        mem := by
          simp only [Partial.mem_iff, Hierarchical.obj?]
          exists LoopModel.Rtr.rcn
          split
          case isTrue h =>
            have o := h.choose_spec
            obtain ⟨_, ho⟩ := h
            rw [o.unique ho]
            cases ho; cases ‹Member ..›; cases ‹StrictMember ..›
            all_goals simp only [state₀, get?] at ‹_ = some _›
            next _ h => injection h with h; subst h; rfl
            next _ h => contradiction
          case isFalse h =>
            push_neg at h
            exact h _ ⟨.strict (.final rfl)⟩ |>.elim
        deps := by
          intro i h
          rw [dependencies, Set.mem_setOf] at h
          -- h should be a contradiction, as r doesnt have any dependencies
          sorry
        unprocessed _ := by contradiction
      }
      (by sorry)
      (by sorry)


private theorem LoopModel.execution₀_length_le (microstep : Nat) :
    microstep ≤ (execution₀ microstep).length := by
  induction microstep
  case zero => rfl
  case succ => rw [execution₀, length, length]; omega

-- Properness of a finite reactor model is not sufficient for finite variability. This is a
-- consequence of logical tags being super-dense.
--
-- Proof Idea: Construct a reactor with a reaction which always schedules and action for the
--             current logical time. This only ever increases the micro-step, but not the time.
open LoopModel in
theorem not_finitely_variable : ¬∀ (α) [Proper α] [Reactor.Finite α], FiniteVariability α := by
  intro h
  have ⟨b, h⟩ := h _ ⟨1, 0⟩ (state₀ 0)
  have := h (execution₀ b) Time.Tag.lt_of_lt_time
  have := execution₀_length_le b
  omega
