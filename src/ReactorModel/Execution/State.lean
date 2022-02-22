import ReactorModel.Execution.Context
import ReactorModel.Execution.Dependency

structure Execution.State where
  rtr : Reactor
  ctx : Context

namespace Execution.State

structure couldExec (s : State) (i : ID) : Prop where
  deps : s.rtr.dependencies i ⊆ s.ctx.currentExecutedRcns
  unexeced : i ∉ s.ctx.currentExecutedRcns
  mutsBeforeNorms : ∃ iₚ p rcn, (s.rtr &[Cmp.rcn:i]= iₚ) ∧ (s.rtr *[Cmp.rtr:iₚ]= p) ∧ (p.rcns i = some rcn) ∧ (rcn.isNorm → p.muts.ids ⊆ s.ctx.currentExecutedRcns)

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

def freshID (s : State) : ID := s.ctx.freshID s.rtr

theorem freshID_fresh (s : State) : ∀ cmp, s.freshID ∉ s.rtr.ids cmp :=
  λ cmp => s.ctx.freshIDCorrect s.rtr cmp

end Execution.State 