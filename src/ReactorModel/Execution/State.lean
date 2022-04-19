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
  | some ⟨_, rtr⟩, some rcn => some {
      portVals := rtr.ports.restrict (rcn.deps Role.in) |>.map (·.val),
      acts :=     rtr.acts.filterMap (· s.ctx.time) |>.restrict (rcn.deps Role.in),
      state :=    rtr.state,
      time :=     s.ctx.time
    }
  | _, _ => none

theorem rcnInput_some_iff_rtr_contains_rcn {s : State} :
  (s.rcnInput i = some j) ↔ s.rtr.contains .rcn i := 
  sorry

noncomputable def rcnOutput (s : State) (i : ID) : Option (List Change) :=
  match s.rtr.obj? .rcn i, s.rcnInput i with
  | some rcn, some i => rcn i 
  | _, _ => none

theorem rcnOutput_dep_only {s : State} {i : ID} (v) : 
  (s.rtr.obj? .rcn i = some rcn) → (s.rcnOutput i = some o) → (p ∉ rcn.deps Role.out) → Change.port p v ∉ o :=
  sorry 

theorem rtr_contains_rcn_if_rcnOutput_some {s : State} :
  (s.rcnOutput rcn = some o) → s.rtr.contains .rcn rcn :=
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