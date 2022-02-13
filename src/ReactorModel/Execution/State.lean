import ReactorModel.Execution.Context

structure Execution.State where
  rtr : Reactor
  ctx : Context

namespace Execution.State

def nextTag (s : State) : Option Time.Tag :=
  s.rtr.scheduledTags.filter (s.ctx.time < ·) |>.min

theorem time_lt_nextTag {s : State} {g : Time.Tag} :
  (s.nextTag = g) → s.ctx.time < g := by 
  intro h
  simp only [nextTag] at h
  exact Finset.mem_of_min h |> (Finset.mem_filter _).mp |> And.right

end Execution.State 