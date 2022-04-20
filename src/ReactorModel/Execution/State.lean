import ReactorModel.Execution.Context
import ReactorModel.Execution.Dependency

open Port

@[ext]
structure Execution.State where
  rtr : Reactor
  ctx : Context

namespace Execution.State

structure allows (s : State) (i : ID) : Prop where
  deps : s.rtr.dependencies i ⊆ s.ctx.currentProcessedRcns
  unprocessed : i ∉ s.ctx.currentProcessedRcns

noncomputable def rcnInput (s : State) (i : ID) : Option Reaction.Input := 
  match s.rtr.con? .rcn i, s.rtr.obj? .rcn i with
  | some con, some rcn => some {
      portVals := con.obj.ports.restrict (rcn.deps Role.in) |>.map (·.val),
      acts :=     con.obj.acts.filterMap (· s.ctx.time) |>.restrict (rcn.deps Role.in),
      state :=    con.obj.state,
      time :=     s.ctx.time
    }
  | _, _ => none

noncomputable def rcnOutput (s : State) (i : ID) : Option (List Change) :=
  match s.rtr.obj? .rcn i, s.rcnInput i with
  | some rcn, some i => rcn i 
  | _, _ => none

theorem rcnInput_to_rcnOutput {s : State} : 
  (s.rcnInput j = some i) → (∃ rcn, s.rtr.obj? .rcn j = some rcn ∧ s.rcnOutput j = rcn i) := by
  intro h
  cases ho : s.rtr.obj? .rcn j
  case none => simp [rcnInput, ho] at h
  case some rcn => exact ⟨rcn, rfl, by simp [rcnOutput, ho, h]⟩ 
    
theorem rcnOutput_to_contains {s : State} :
  (s.rcnOutput rcn = some o) → (s.rtr.contains .rcn rcn) := by
  intro h
  cases ho : s.rtr.obj? .rcn rcn
  case none => simp [rcnOutput, ho] at h
  case some => exact Reactor.contains_iff_obj?.mpr ⟨_, ho⟩

/-
theorem rcnInput_iff_rcnOutput {s : State} : 
  (∃ i, s.rcnInput j = some i) ↔ (∃ o, s.rcnOutput j = some o) := by
  constructor <;> (
    intro h; simp [rcnInput, rcnOutput] at *
    cases ho : s.rtr.obj? .rcn j
    case none => simp [ho] at h
    case some => have ⟨_, hc, _⟩ := Reactor.obj?_to_con?_and_cmp? ho; simp [hc]
  )
-/

theorem rcnOutput_dep_only {s : State} {i : ID} (v) : 
  (s.rtr.obj? .rcn i = some rcn) → (s.rcnOutput i = some o) → (p ∉ rcn.deps Role.out) → Change.port p v ∉ o :=
  sorry 
  
theorem rcnInput_eq_rcnOutput_eq {s₁ s₂ : State} :
  (s₁.rcnInput rcn = s₂.rcnInput rcn) → (s₁.rcnOutput rcn = s₂.rcnOutput rcn) := 
  sorry

def triggers (s : State) (i : ID) : Prop :=
  match s.rtr.obj? .rcn i, s.rcnInput i with
  | some rcn, some i => rcn.triggersOn i 
  | _, _ => False

def nextTag (s : State) : Option Time.Tag :=
  s.rtr.scheduledTags.filter (s.ctx.time < ·) |>.min

theorem time_lt_nextTag {s : State} {g : Time.Tag} :
  (s.nextTag = g) → s.ctx.time < g := by 
  intro h
  simp only [nextTag] at h
  exact Finset.mem_of_min h |> (Finset.mem_filter _).mp |> And.right

def freshID (s : State) : Rooted ID → ID := s.ctx.freshID.func s.rtr

end Execution.State 