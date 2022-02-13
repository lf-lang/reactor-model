import ReactorModel.Execution.Context
import ReactorModel.Execution.Dependency

structure Execution.State where
  rtr : Reactor
  ctx : Context

namespace Execution.State

structure couldExec (s : State) (rcn : ID) : Prop where
  deps : s.rtr.dependencies rcn ⊆ s.ctx.currentExecutedRcns
  unexeced : rcn ∉ s.ctx.currentExecutedRcns

def triggers (s : State) (rcn : Reaction) : Prop :=
  rcn.triggersOn $ s.rtr.inputForRcn rcn s.ctx.time

noncomputable def outputOf (s : State) (rcn : Reaction) : List Change :=
  rcn $ s.rtr.inputForRcn rcn s.ctx.time

def nextTag (s : State) : Option Time.Tag :=
  s.rtr.scheduledTags.filter (s.ctx.time < ·) |>.min

theorem time_lt_nextTag {s : State} {g : Time.Tag} :
  (s.nextTag = g) → s.ctx.time < g := by 
  intro h
  simp only [nextTag] at h
  exact Finset.mem_of_min h |> (Finset.mem_filter _).mp |> And.right

end Execution.State 