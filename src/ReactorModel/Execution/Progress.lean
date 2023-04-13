import ReactorModel.Execution.Trace
import ReactorModel.Determinism.Execution

open ReactorType Classical

-- TODO: Move the Determinism folder into the Execution folder.
--       Perhaps also rename it to Theorems, as it contains many lemmas which aren't only relevant
--       to proving determinism.

namespace Execution

variable [Proper α]

structure State.Terminal (s : State α) : Prop where
  closed  : s.Closed
  no_next : ∀ g, ¬s.NextTag g

namespace State
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
def Progress (rtr : α) : Prop :=
  ∀ s, (s.rtr = rtr) → ¬s.Terminal → (∃ s', s ⇓ s')    

namespace Progress

variable {rtr : α}

-- TODO: Factor out a lemma of the form "reactors with no reactions are acyclic."
theorem to_deps_acyclic_triv (triv : rtr[.rcn] = ∅) (p : Progress rtr) : 
    Dependency.Acyclic rtr := by
  simp_all [Dependency.Acyclic.iff_mem_acyclic, triv]
  intros _ h
  exact absurd h Partial.not_mem_empty

theorem to_deps_acyclic_nontriv (nontriv : rtr[.rcn].Nonempty) (p : Progress rtr) : 
    Dependency.Acyclic rtr := by
  simp [Dependency.Acyclic.iff_mem_acyclic]
  intro rcn hm
  let s : State α := { rtr, tag := 0, progress := ∅ }
  have : s.Nontrivial := ⟨nontriv⟩ 
  have hc : ¬s.Closed := (Set.not_nonempty_empty ·.progress_Nonempty)
  have ⟨_, e⟩ := p s rfl (State.Terminal.not_of_not_closed hc)
  have ⟨e⟩ := e.resolve_close hc 
  exact e.acyclic $ e.progress_empty_mem_rcns_iff rfl |>.mpr hm

theorem to_deps_acyclic : (Progress rtr) → Dependency.Acyclic rtr :=
  if h : rtr[.rcn].Nonempty 
  then to_deps_acyclic_nontriv h 
  else to_deps_acyclic_triv (Partial.Nonempty.not_to_empty h)

theorem of_deps_acyclic (a : Dependency.Acyclic rtr) : Progress rtr := by
  intro s hs ht
  by_cases hc : s.Closed
  case pos =>
    have ⟨g, hg⟩ := State.Terminal.not_elim ht |>.resolve_left (not_not.mpr hc)
    sorry -- by_contra
    -- Can you avoid proving that you can clear ports by going for proof by contra?
  case neg =>
    have : s.Nontrivial := byContradiction (hc $ State.Trivial.of_not_nontrivial · |>.closed)
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