import ReactorModel.Execution.Trace
import ReactorModel.Determinism.ExecutionStep

open ReactorType

-- TODO: Move the Determinism folder into the Execution folder.
--       Perhaps also rename it to Theorems, as it contains many lemmas which aren't only relevant
--       to proving determinism.

namespace Execution

variable [Proper α]

structure State.Terminal (s : State α) : Prop where
  closed  : s.Closed
  no_next : ∀ g, ¬s.NextTag g

theorem State.Terminal.not_of_not_closed {s : State α} (h : ¬s.Closed) : ¬State.Terminal s :=
  (h ·.closed)

-- A reactor has the progress property, if from any nonterminal state based at that reactor, we can 
-- perform an execution step.
def Progress (rtr : α) : Prop :=
  ∀ s, (s.rtr = rtr) → ¬s.Terminal → (∃ s', Nonempty $ s ⇓ s')    

theorem Progress.iff_deps_acyclic {rtr : α} : (Progress rtr) ↔ (Dependency.Acyclic rtr) := by
  simp [Dependency.Acyclic.iff_mem_acyclic]
  constructor <;> intro h
  case mp =>
    intro rcn hm
    let s : State α := { rtr, tag := 0, progress := ∅ }
    have hc : ¬s.Closed := sorry -- for nontrivial state: follows from progress = ∅.
    have ⟨_, ⟨e⟩⟩ := h s rfl (State.Terminal.not_of_not_closed hc)
    replace e := e.resolve_close hc 
    exact e.acyclic $ e.progress_empty_mem_rcns_iff rfl |>.mpr hm
  case mpr =>
    sorry
    -- Perhaps you can avoid proving directly that you can perform clearing ports by using a proof by
    -- contradiction.

end Execution