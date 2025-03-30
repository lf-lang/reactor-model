import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.State
import ReactorModel.Execution.Theorems.Variability.Loop.Reactor
import ReactorModel.Execution.Theorems.Execution

noncomputable section
open Reactor Execution

namespace Loop

def state₀ (microstep : Nat) : State Reactor where
  rtr := { act := true }
  tag := ⟨0, microstep⟩
  progress := ∅
  events
    | .r => none
    | .a => actionEvents microstep
where
  actionEvents : Nat → Time.Tag ⇉ Bool
    | 0     => .singleton ⟨0, 0⟩ true
    | m + 1 => (actionEvents m).insert ⟨0, m + 1⟩ true

theorem state₀_schedule_actionEvents (m) :
    State.schedule.go (α := Reactor) (state₀.actionEvents m) 0 true = state₀.actionEvents (m + 1) := by
  sorry

def execution₀ : (microstep : Nat) → Execution (state₀ 0) (state₀ microstep)
  | 0     => .refl
  | m + 1 =>
    let e := execution₀ m
    let s₁ := state₀ m |>.schedule .a 0 true |>.record .r
    let s₂ := state₀ (m + 1)
    let timeStep : s₁ ↓ₜ s₂ := sorry
    execution₀ m |>.push (.exec <| execStep m) |>.push (.time timeStep)
where
  execStep (m) : (state₀ m) ↓ₑ (state₀ m |>.schedule .a 0 true |>.record .r) :=
    .mk execStep_allows execStep_triggers execStep_apply
  execStep_allows {m} : (state₀ m).Allows .r := {
      mem           := by simp [Partial.mem_iff]
      deps          := by simp [dependencies, no_deps]
      unprocessed _ := by contradiction
    }
  execStep_triggers {m} : (state₀ m).Triggers .r :=
    .intro (obj?_rcn_r _) <| by
      exists ⟨.act, .a⟩, true
      simp [rcn, state₀, State.input, State.input.restriction, Partial.restrict]
  execStep_apply {m} : (state₀ m) -[(state₀ m).output .r]→ (state₀ m |>.schedule .a 0 true) := by
    simp only [obj?_rcn_r, rcn, State.input, State.output, Option.elim_some]
    exact Step.Apply.RTC.trans .act .refl
  timeStep (m) : (state₀ m |>.schedule .a 0 true |>.record .r) ↓ₜ (state₀ <| m + 1) :=
    let s₁ := state₀ m |>.schedule .a 0 true |>.record .r
    let s₂ := { s₁ with rtr := s₁.rtr, tag := ⟨0, m + 1⟩, progress := ∅ }
    have h : s₂ = (state₀ <| m + 1) := by
      simp only [state₀, State.record_preserves_rtr, State.schedule_preserves_rtr,
                 State.record_preserves_events, State.mk.injEq, true_and, s₂, s₁, State.schedule]
      funext i
      cases i <;> simp only [Partial.update, reduceCtorEq, ↓reduceIte, Option.map_eq_map,
                             Option.map_some', state₀_schedule_actionEvents, s₂, s₁]
    h ▸ .mk timeStep_closed timeStep_next timeStep_refresh
  timeStep_closed {m} : (state₀ m |>.schedule .a 0 true |>.record .r).Closed := by
    rw [State.Closed, rcn_ids]
    simp [State.schedule_preserves_progress, State.record_progress_eq, state₀, Set.insert]
  timeStep_next {m} : (state₀ m |>.schedule .a 0 true |>.record .r).NextTag ⟨0, m + 1⟩ := {
      mem   := timeStep_next_mem
      bound := sorry
      least := sorry
    }
  timeStep_next_mem {m} : ⟨0, m + 1⟩ ∈ (((state₀ m).schedule .a 0 true).record .r).scheduledTags := by
    exists .a
    simp [State.scheduledTags, State.schedule, state₀, Partial.update, State.schedule.go, state₀.actionEvents]
    induction m
    case zero =>
      simp [state₀.actionEvents]
      split
      · contradiction
      next h =>
        have ⟨h, _⟩ := Finset.mem_filter.mp <| Finset.mem_of_max h
        simp only [Finset.mem_singleton, Time.Tag.mk.injEq] at h
        simp [h.right, Finmap.mem_keys]
    case succ ih =>
      simp [state₀.actionEvents]
      split
      next m _ h =>
        have := Finset.filter_eq_empty_iff.mp (Finset.max_eq_bot.mp h) (x := ⟨0, m + 1⟩) (by simp [Finmap.mem_keys])
        contradiction
      · sorry
  timeStep_refresh {m} :
      Refresh (state₀ m |>.schedule .a 0 true |>.record .r).rtr
              (state₀ m |>.schedule .a 0 true |>.record .r).rtr
              ((state₀ m |>.schedule .a 0 true |>.record .r).actions ⟨0, m + 1⟩) := {
      equiv    := .refl _
      eq_state := rfl
      inputs   := by simp
      outputs  := by simp
      acts     := by
        simp [State.actions]
        sorry
    }

theorem execution₀_length_le (microstep : Nat) : microstep ≤ (execution₀ microstep).length := by
  induction microstep
  case zero => rfl
  case succ => simp [execution₀, Nat.le_add_right_of_le, *]
