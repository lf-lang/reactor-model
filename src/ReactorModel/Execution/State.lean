import ReactorModel.Execution.Context
import ReactorModel.Execution.Dependency

@[ext]
structure Execution.State where
  rtr : Reactor
  ctx : Context

namespace Execution.State

structure allows (s : State) (i : ID) : Prop where
  deps : s.rtr.dependencies i ⊆ s.ctx.currentProcessedRcns
  unexeced : i ∉ s.ctx.currentProcessedRcns

noncomputable def rcnInput (s : State) (rcn : Reaction) : Reaction.Input :=
  s.rtr.inputForRcn rcn s.ctx.time

def triggers (s : State) (rcn : Reaction) : Prop :=
  rcn.triggersOn $ s.rcnInput rcn

def nextTag (s : State) : Option Time.Tag :=
  s.rtr.scheduledTags.filter (s.ctx.time < ·) |>.min

theorem time_lt_nextTag {s : State} {g : Time.Tag} :
  (s.nextTag = g) → s.ctx.time < g := by 
  intro h
  simp only [nextTag] at h
  exact Finset.mem_of_min h |> (Finset.mem_filter _).mp |> And.right

def freshID (s : State) : Rooted ID → ID := s.ctx.freshID.func s.rtr

end Execution.State 