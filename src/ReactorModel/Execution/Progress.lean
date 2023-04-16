import ReactorModel.Execution.Trace
import ReactorModel.Determinism.Execution

noncomputable section
open ReactorType Practical FiniteUpdatable Classical

-- TODO: Move the Determinism folder into the Execution folder.
--       Perhaps also rename it to Theorems, as it contains many lemmas which aren't only relevant
--       to proving determinism.

namespace ReactorType

variable [Practical α]

def clear (rtr : α) : α :=
  update' (update' rtr .inp .absent) .out .absent

open FiniteUpdatable in
theorem clear_cleared (rtr : α) : Cleared rtr (clear rtr) where
  equiv := Equivalent.trans update'_equiv update'_equiv
  eq_state := by
    rw [clear, update'_preserves (by simp : .stv ≠ .out), update'_preserves (by simp : .stv ≠ .inp)]
  eq_acts := by
    rw [clear, update'_preserves (by simp : .act ≠ .out), update'_preserves (by simp : .act ≠ .inp)]
  inputs := by 
    rw [clear, update'_preserves (by simp : .inp ≠ .out), update'_updated] 
  outputs := by 
    rw [clear, update'_updated, update'_preserves (by simp : .out ≠ .inp)] 

end ReactorType

namespace Execution
namespace State

variable [Practical α]

protected structure Over (rtr : α) extends State α where 
  rtr_eq       : toState.rtr = rtr
  progress_sub : progress ⊆ rtr[.rcn].ids 

instance {rtr : α} : Coe (State.Over rtr) (State α) where
  coe := State.Over.toState

theorem Over.not_closed_to_nontrivial {rtr : α} {s : State.Over rtr} (h : ¬s.Closed) : 
    s.Nontrivial := by
  by_contra hn
  have ht' := State.Trivial.of_not_nontrivial hn
  have hp := s.progress_sub
  simp [State.Closed, ht', Partial.empty_ids, Set.subset_empty_iff] at h hp
  contradiction

structure Terminal (s : State α) : Prop where
  closed  : s.Closed
  no_next : ∀ g, ¬s.NextTag g

namespace Terminal

variable {s : State α}

theorem not_of_not_closed (h : ¬s.Closed) : ¬State.Terminal s :=
  (h ·.closed)

theorem not_of_next_tag (h : s.NextTag g) : ¬State.Terminal s :=
  (·.no_next g h)

theorem not_elim (t : ¬s.Terminal) : ¬s.Closed ∨ (∃ g, s.NextTag g) := by
  by_contra h
  push_neg at h
  exact t ⟨h.left, h.right⟩ 

end Terminal
end State

-- A reactor has the progress property, if from any nonterminal state based at that reactor, we can 
-- perform an execution step.
def Progress [Practical α] (rtr : α) : Prop :=
  ∀ (s : State.Over rtr), ¬s.Terminal → (∃ s' : State α, s ⇓ s')    

namespace Progress

variable [Practical α] {rtr : α} in section

theorem to_deps_acyclic_nontriv (nontriv : rtr[.rcn].Nonempty) (p : Progress rtr) : 
    Dependency.Acyclic rtr := by
  simp [Dependency.Acyclic.iff_mem_acyclic]
  intro rcn hm
  let s : State α := { rtr, tag := 0, progress := ∅ }
  have : s.Nontrivial := ⟨nontriv⟩ 
  have hc : ¬s.Closed := (Set.not_nonempty_empty ·.progress_Nonempty)
  have ⟨_, e⟩ := p ⟨s, rfl, by simp⟩ (State.Terminal.not_of_not_closed hc)
  have ⟨e⟩ := e.resolve_close hc 
  exact e.acyclic $ e.progress_empty_mem_rcns_iff rfl |>.mpr hm

theorem to_deps_acyclic : (Progress rtr) → Dependency.Acyclic rtr :=
  if h : rtr[.rcn].Nonempty 
  then to_deps_acyclic_nontriv h 
  else fun _ => Dependency.Acyclic.of_trivial (Partial.Nonempty.not_to_empty h)

end

variable [Practical α] {rtr : α}

theorem of_deps_acyclic (a : Dependency.Acyclic rtr) : Progress rtr := by
  intro s ht
  by_cases hc : s.Closed
  case pos =>
    have ⟨g, hg⟩ := State.Terminal.not_elim ht |>.resolve_left (not_not.mpr hc)
    exact ⟨⟨clear s.rtr, g, ∅⟩, .advance ⟨hc, ⟨hg, clear_cleared _⟩⟩⟩
  case neg =>
    have := s.not_closed_to_nontrivial hc
    -- This might be the place to break out a lemma that works at the level of instantaneous
    -- execution steps. On that level you can show that there exists a reaction that doesn't have
    -- any unprocessed dependencies (assuming the reactor is nontrivial). Then you can show that you
    -- can create an instantaneous step for that reaction by performing a case distinction on
    -- whether the reaction is triggered or not - in both cases you can create a step.
    -- Then you need to show that we can repeat this process for all unprocessed reactions, thus
    -- obtaining an closed instantaneous execution.
    sorry

theorem iff_deps_acyclic : (Progress rtr) ↔ (Dependency.Acyclic rtr) :=
  ⟨to_deps_acyclic, of_deps_acyclic⟩

end Progress
end Execution