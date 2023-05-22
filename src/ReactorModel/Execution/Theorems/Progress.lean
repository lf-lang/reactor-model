import ReactorModel.Execution.Theorems.StateOver

noncomputable section
open ReactorType Classical

namespace Execution

variable [Proper α] [ReactorType.Finite α] {rtr : α} {s : State.Over rtr} 

def Step.Time.construct (ht : ¬s.Terminal) (hc : s.Closed) : (s' : State α) × (s ↓ₜ s') :=
  let g := State.Terminal.not_elim ht |>.resolve_left (not_not.mpr hc)
  let s' := ⟨refresh s.rtr (s.actions g.choose), g.choose, ∅, s.events⟩
  ⟨s', hc, g.choose_spec, refresh_correct _ $ Partial.mapIdx_ids ..⟩

def Step.construct (a : Dependency.Acyclic rtr) (hc : ¬s.Closed) : (s' : State α) × (s ↓ s') := 
  let rcn := s.allowed a hc
  if h : s.Triggers rcn
  then ⟨_, .exec ⟨rcn.property, h, Step.Apply.RTC.construct s.toState (s.output rcn) |>.snd⟩⟩
  else ⟨_, .skip ⟨rcn.property, h⟩⟩ 

-- A reactor has the progress property, if from any nonterminal state based at that reactor, we can 
-- perform an execution step.
def Progress [Indexable α] (rtr : α) : Prop :=
  ∀ (s : State.Over rtr), ¬s.Terminal → ∃ s' : State α, Nonempty (s ↓ s')    

namespace Progress

theorem to_deps_acyclic_nontriv (nontriv : rtr[.rcn].Nonempty) (p : Progress rtr) : 
    Dependency.Acyclic rtr := by
  simp [Dependency.Acyclic.iff_mem_acyclic]
  intro rcn hm
  let s : State α := { rtr, tag := 0, progress := ∅, events := ∅ }
  have n : s.Nontrivial := nontriv
  have hc : ¬s.Closed := (Set.not_nonempty_empty $ ·.progress_nonempty n)
  have ⟨_, e⟩ := p ⟨s, rfl, by simp, sorry⟩ (State.Terminal.not_of_not_closed hc)
  have ⟨e⟩ := e.resolve_close hc 
  exact e.acyclic $ e.progress_empty_mem_rcns_iff rfl |>.mpr hm

theorem to_deps_acyclic : (Progress rtr) → Dependency.Acyclic rtr :=
  if h : rtr[.rcn].Nonempty 
  then to_deps_acyclic_nontriv h 
  else fun _ => Dependency.Acyclic.of_trivial (Partial.Nonempty.not_to_empty h)

theorem of_deps_acyclic (a : Dependency.Acyclic rtr) : Progress rtr := by
  intro s ht
  if hc : s.Closed then 
    have ⟨_, a⟩ := Advance.of_nonterminal_closed ht hc
    exact ⟨_, .advance a⟩
  else 
    have ⟨_, ⟨e⟩⟩ := Instantaneous.ClosedExecution.of_acyclic_not_closed a hc
    exact ⟨_, .close e⟩

theorem iff_deps_acyclic : (Progress rtr) ↔ (Dependency.Acyclic rtr) :=
  ⟨to_deps_acyclic, of_deps_acyclic⟩

end Progress
end Execution