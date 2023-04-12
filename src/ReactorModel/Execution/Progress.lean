import ReactorModel.Execution.Trace

open ReactorType

-- TODO: Move the Determinism folder into the Execution folder.
--       Perhaps also rename it to Theorems, as it contains many lemmas which aren't only relevant
--       to proving determinism.

namespace Execution

variable [Proper α]

structure State.Terminal (s : State α) : Prop where
  closed  : s.Closed
  no_next : ∀ g, ¬s.NextTag g

-- A reactor has the progress property, if from any nonterminal state based at that reactor, we can 
-- perform an execution step.
-- TODO: This isn't exactly what we want. The freshness condition is too restrictive.
def Progress (rtr : α) : Prop :=
  ∀ {s : State α}, (s.rtr = rtr) → (s.progress = ∅) → ¬s.Terminal → (∃ s', s ⇓ s')    

theorem Progress.iff_deps_acyclic {rtr : α} : (Progress rtr) ↔ (Dependency.Acyclic rtr) :=
  sorry

end Execution