import ReactorModel.Execution.Theorems.StateOver

noncomputable section
open Reactor Classical

namespace Execution

variable [Hierarchical α]

-- A state `s` is stuck, if there does not exist a valid execution step starting at `s`.
def State.Stuck (s : State α) : Prop :=
  ¬∃ s', Nonempty (Step s s')

theorem State.Stuck.not_iff {s : State α} : ¬s.Stuck ↔ ∃ s', Nonempty (Step s s') := by
  simp [State.Stuck]

-- A reactor `rtr` has the progress property, if non-terminal states based at `rtr` are not stuck.
def Progress (rtr : α) : Prop :=
  ∀ (s : State.Over rtr), ¬s.Terminal → ¬s.Stuck

namespace Progress

theorem to_deps_acyclic {rtr : α} (p : Progress rtr) : Dependency.Acyclic rtr := by
  simp only [Dependency.Acyclic.iff_mem_acyclic]
  intro rcn hm
  have ⟨_, ⟨e⟩⟩ := State.Stuck.not_iff.mp <| p _ <| State.Over.forcing_not_terminal hm
  cases e
  case time e => exact State.Over.forcing_not_time_step e hm |>.elim
  case skip e => exact State.Over.forcing_skip_step_rcn_eq e ▸ e.allows_rcn.acyclic
  case exec e => exact State.Over.forcing_exec_step_rcn_eq e ▸ e.allows_rcn.acyclic

variable {α} [Proper α] [Reactor.Finite α] {rtr : α}

theorem of_deps_acyclic (a : Dependency.Acyclic rtr) : Progress rtr :=
  fun s ht =>
    State.Stuck.not_iff.mpr <|
      if hc : s.Closed then
        let ⟨_, hg⟩ := State.Terminal.not_elim ht |>.resolve_left (not_not.mpr hc)
        ⟨_, ⟨.time ⟨hc, hg, refresh_correct _ <| Partial.mapIdx_ids ..⟩⟩⟩
      else
        let ⟨rcn, hr⟩ := s.exists_allowed_of_acyclic_not_closed a hc
        if h : s.Triggers rcn
        then ⟨_, ⟨.exec ⟨hr, h, Step.Apply.RTC.construct .. |>.snd⟩⟩⟩
        else ⟨_, ⟨.skip ⟨hr, h⟩⟩⟩

theorem iff_deps_acyclic : (Progress rtr) ↔ (Dependency.Acyclic rtr) :=
  ⟨to_deps_acyclic, of_deps_acyclic⟩

end Execution.Progress
