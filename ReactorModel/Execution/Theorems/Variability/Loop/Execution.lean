import ReactorModel.Execution.Theorems.Step.Basic
import ReactorModel.Execution.Theorems.State
import ReactorModel.Execution.Theorems.Variability.Loop.Reactor
import ReactorModel.Execution.Theorems.Execution

noncomputable section
open Reactor Execution

namespace Loop

def state₀ (μ : Nat) : State Reactor where
  rtr := { act := true }
  tag := ⟨0, μ⟩
  progress := ∅
  events
    | .r => none
    | .a => actionEvents μ
where
  actionEvents : Nat → Time.Tag ⇉ Bool
    | 0     => .singleton ⟨0, 0⟩ true
    | m + 1 => (actionEvents m).insert ⟨0, m + 1⟩ true

theorem state₀_actionEvents_keys_time : ∀ i ∈ (state₀.actionEvents μ).keys, i.time = 0 := by
  intro i h
  induction μ
  case zero => simp_all [state₀.actionEvents]
  case succ ih =>
    simp only [Finmap.mem_keys, state₀.actionEvents, Finmap.mem_insert] at *
    cases h <;> simp_all

@[simp]
theorem state₀_actionEvents_keys_max (μ) : (state₀.actionEvents μ).keys.max = some ⟨0, μ⟩ := by
  induction μ
  case zero => rfl
  case succ μ ih =>
    simp only [state₀.actionEvents, Finmap.insert_keys, Finset.max_insert, ih]
    have := Time.Tag.lt_of_lt_microstep (t := 0) (m₁ := μ) (m₂ := μ + 1) (h := by simp)
    exact max_eq_left_of_lt <| (WithBot.unbotD_lt_iff fun a => this).mp this

theorem state₀_schedule_actionEvents :
    (μ : Nat) →
    State.schedule.go (α := Reactor) (state₀.actionEvents μ) 0 true =
    state₀.actionEvents (μ + 1)
  | .zero => rfl
  | .succ _ => by
    rw (occs := [2]) [state₀.actionEvents]
    simp [State.schedule.go]
    split <;> simp only [Finset.filter_true_of_mem state₀_actionEvents_keys_time,
                         state₀_actionEvents_keys_max, reduceCtorEq] at *
    · injections; simp_all

theorem state₀_allows_r (μ) : (state₀ μ).Allows .r where
  mem           := by simp [Partial.mem_iff]
  deps          := by simp [dependencies, no_deps]
  unprocessed _ := by contradiction

theorem state₀_triggers_r (μ) : (state₀ μ).Triggers .r := by
  apply State.Triggers.intro (obj?_rcn_r _)
  exists ⟨.act, .a⟩, true
  simp [rcn, state₀, State.input, State.input.restriction, Partial.restrict]

def applyState₀ (μ) : (state₀ μ) -[(state₀ μ).output .r]→ (state₀ μ |>.schedule .a 0 true) := by
  simp only [obj?_rcn_r, rcn, State.input, State.output, Option.elim_some]
  exact Step.Apply.RTC.trans .act .refl

abbrev closedState₀ (μ : Nat) : State Reactor :=
  state₀ μ |>.schedule .a 0 true |>.record .r

def stepToClosedState₀ (μ : Nat) : Step (state₀ μ) (closedState₀ μ) :=
  .exec <| .mk (state₀_allows_r μ) (state₀_triggers_r μ) (applyState₀ μ)

theorem closedState₀_closed (μ) : (closedState₀ μ).Closed := by
  rw [State.Closed, rcn_ids]
  simp [State.schedule_preserves_progress, State.record_progress_eq, state₀, Set.insert]

theorem closedState₀_nextTag_mem_scheduled (μ) : ⟨0, μ + 1⟩ ∈ (closedState₀ μ).scheduledTags := by
  exists .a
  simp [State.schedule, Finmap.mem_keys, state₀, state₀_schedule_actionEvents, state₀.actionEvents]

theorem closedState₀_nextTag (μ) : (closedState₀ μ).NextTag ⟨0, μ + 1⟩ where
  mem       := closedState₀_nextTag_mem_scheduled μ
  bound     := by simp [state₀, Time.Tag.lt_of_lt_microstep]
  least _ _ := Time.Tag.lt_microstep_to_le_succ_microstep

@[simp]
theorem closedState₀_action_a (μ) : (closedState₀ μ).actions ⟨0, μ + 1⟩ .a = true := by
  sorry

@[simp]
theorem closedState₀_action_r (μ) : (closedState₀ μ).actions ⟨0, μ + 1⟩ .r = none := by
  simp only [State.actions, State.record_preserves_events, Option.bind_eq_bind,
    State.record_preserves_rtr, State.schedule_preserves_rtr, Option.eq_none_iff_forall_not_mem,
    Option.mem_def]
  apply forall_not_of_not_exists
  simp only [← Partial.mem_iff, State.record_preserves_rtr, State.schedule_preserves_rtr,
    Partial.mem_def, Partial.mapIdx_ids]
  simp [←Partial.mem_def, Partial.mem_iff]

theorem closedState₀_refresh (μ) :
    Refresh (closedState₀ μ).rtr (closedState₀ μ).rtr ((closedState₀ μ).actions ⟨0, μ + 1⟩) where
  equiv    := .refl _
  eq_state := rfl
  inputs   := by simp
  outputs  := by simp
  acts     := by ext i a; cases i <;> simp [state₀]

def stepFromClosedState₀ (μ : Nat) : Step (closedState₀ μ) (state₀ <| μ + 1) :=
  .time <| dst_cast ▸ .mk (closedState₀_closed μ) (closedState₀_nextTag μ) (closedState₀_refresh μ)
where
  dst_cast : (state₀ <| μ + 1) = { closedState₀ μ with tag := ⟨0, μ + 1⟩, progress := ∅ } := by
    simp only [state₀, State.record_preserves_rtr, State.schedule_preserves_rtr,
                State.record_preserves_events, State.mk.injEq, true_and, State.schedule]
    funext i
    cases i <;> simp [Partial.update, state₀_schedule_actionEvents]

def execution₀ : (μ : Nat) → Execution (state₀ 0) (state₀ μ)
  | 0     => .refl
  | m + 1 => execution₀ m |>.push (stepToClosedState₀ m) |>.push (stepFromClosedState₀ m)

theorem execution₀_length_le (μ : Nat) : μ ≤ (execution₀ μ).length := by
  induction μ
  case zero => rfl
  case succ => simp [execution₀, Nat.le_add_right_of_le, *]
