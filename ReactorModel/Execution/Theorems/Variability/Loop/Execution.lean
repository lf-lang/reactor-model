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

theorem state₀_schedule_actionEvents (μ) :
    State.schedule.go (α := Reactor) (state₀.actionEvents μ) 0 true = state₀.actionEvents (μ + 1) := by
  sorry

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
  simp [State.scheduledTags, State.schedule, state₀, Partial.update, State.schedule.go, state₀.actionEvents]
  induction μ
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

theorem closedState₀_nextTag (μ) : (closedState₀ μ).NextTag ⟨0, μ + 1⟩ where
  mem   := closedState₀_nextTag_mem_scheduled μ
  bound := sorry
  least := sorry

theorem closedState₀_refresh (μ) :
    Refresh (closedState₀ μ).rtr (closedState₀ μ).rtr ((closedState₀ μ).actions ⟨0, μ + 1⟩) where
  equiv    := .refl _
  eq_state := rfl
  inputs   := by simp
  outputs  := by simp
  acts     := by
    simp [State.actions]
    sorry

def stepFromClosedState₀ (μ : Nat) : Step (closedState₀ μ) (state₀ <| μ + 1) :=
  let s₂ := { (closedState₀ μ) with tag := ⟨0, μ + 1⟩, progress := ∅ }
    have h : s₂ = (state₀ <| μ + 1) := by
      simp only [state₀, State.record_preserves_rtr, State.schedule_preserves_rtr,
                 State.record_preserves_events, State.mk.injEq, true_and, s₂, State.schedule]
      funext i
      cases i <;> simp only [Partial.update, reduceCtorEq, ↓reduceIte, Option.map_eq_map,
                             Option.map_some', state₀_schedule_actionEvents, s₂]
  .time <| h ▸ .mk (closedState₀_closed μ) (closedState₀_nextTag μ) (closedState₀_refresh μ)

def execution₀ : (μ : Nat) → Execution (state₀ 0) (state₀ μ)
  | 0     => .refl
  | m + 1 => execution₀ m |>.push (stepToClosedState₀ m) |>.push (stepFromClosedState₀ m)

theorem execution₀_length_le (μ : Nat) : μ ≤ (execution₀ μ).length := by
  induction μ
  case zero => rfl
  case succ => simp [execution₀, Nat.le_add_right_of_le, *]
