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

def unprocessed (s : State α) : Set ID :=
  { i ∈ s.rtr[.rcn] | i ∉ s.progress }

protected structure Over (ovr : α) extends State α where 
  rtr_eq       : rtr = ovr := by rfl
  progress_sub : progress ⊆ rtr[.rcn].ids 

namespace Over

variable {rtr : α} {s : State.Over rtr}

instance : Coe (State.Over rtr) (State α) where
  coe := State.Over.toState

theorem progress_finite (s : State.Over rtr) : s.progress.Finite :=
  Finite.fin s.rtr .rcn |>.subset s.progress_sub

theorem unprocessed_finite (s : State.Over rtr) : s.unprocessed.Finite := by
  simp [unprocessed, Set.setOf_and, s.rtr_eq]
  apply Set.Finite.inter_of_left $ Finite.fin rtr .rcn

theorem unprocessed_empty_iff_closed : (s.unprocessed = ∅) ↔ s.Closed := by
  sorry

theorem not_closed_to_nontrivial (h : ¬s.Closed) : s.Nontrivial := by
  by_contra hn
  have ht' := State.Trivial.of_not_nontrivial hn
  have hp := s.progress_sub
  simp [State.Closed, ht', Partial.empty_ids, Set.subset_empty_iff] at h hp
  contradiction

theorem allowed_of_acyclic_not_closed [State.Nontrivial s.toState] 
    (a : Dependency.Acyclic rtr) (hc : ¬s.Closed) : ∃ i, s.Allows i := 
  sorry -- somehow by induction over the finite set of reactions

def ofStep {s₁ : State.Over rtr₁} {s₂ : State α} (e : s₁.toState ⇓ᵢ s₂) : State.Over s₂.rtr := 
  { s₂ with 
    progress_sub := by 
      simp [e.progress_eq, ←Equivalent.obj?_rcn_eq e.equiv]
      exact Set.insert_subset.mpr ⟨e.allows_rcn.mem, s₁.progress_sub⟩ 
  }

end Over

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

variable [Practical α] {rtr : α}

namespace Instantaneous
namespace Step

variable {s₁ s₂ : State α}

theorem of_acyclic_not_closed {s : State.Over rtr} (a : Dependency.Acyclic rtr) (hc : ¬s.Closed) : 
    ∃ s' : State α, Nonempty (s ⇓ᵢ s') := 
  have := s.not_closed_to_nontrivial hc
  let ⟨rcn, ha⟩ := s.allowed_of_acyclic_not_closed a hc
  if h : s.Triggers rcn
  then ⟨s.exec rcn |>.record rcn, ⟨.exec ha h⟩⟩
  else ⟨s.record rcn, ⟨.skip ha h⟩⟩  

theorem unprocessed₂_eq (e : s₁ ⇓ᵢ s₂) : s₂.unprocessed = s₁.unprocessed \ {e.rcn} := by
  ext i
  simp [State.unprocessed, Equivalent.obj?_rcn_eq e.equiv, and_assoc]
  intro _
  have h := e.mem_progress_iff (rcn' := i) |>.not
  push_neg at h
  simp [and_comm, h]
  
theorem unprocessed₁_eq (e : s₁ ⇓ᵢ s₂) : s₁.unprocessed = insert e.rcn s₂.unprocessed := by
  sorry

end Step

theorem ClosedExecution.of_nonterminal_acyclic_not_closed {s : State.Over rtr} 
    (ht : ¬s.Terminal) (a : Dependency.Acyclic rtr) (hc : ¬s.Closed) : ∃ s' : State α, Nonempty (s ⇓| s') := by
  generalize hp : s.unprocessed = u
  have hu := hp ▸ s.unprocessed_finite
  induction u, hu using Set.Finite.dinduction_on generalizing s rtr
  case _ =>
    exact absurd (State.Over.unprocessed_empty_iff_closed.mp hp) hc
  case _ rcn r u hr hi =>
    have ⟨sₑ, ⟨e⟩⟩ := Instantaneous.Step.of_acyclic_not_closed a hc
    by_cases hc' : sₑ.Closed
    case pos => exact ⟨_, ⟨.single e, hc'⟩⟩ 
    case neg =>
      suffices hs : (State.Over.ofStep e).unprocessed = r by
        have a' := Dependency.Acyclic.equiv e.equiv (s.rtr_eq.symm ▸ a)
        have ht' := State.Terminal.not_of_not_closed hc'
        have ⟨_, ⟨e'⟩⟩ := hi (s := State.Over.ofStep e) ht' a' hc' hs
        exact ⟨_, ⟨.trans e e'.exec, e'.closed⟩⟩ 
      -- Is this provable, or do we need to adjust the way we do induction here?
      clear hi ht hc a hc'
      simp [State.Over.ofStep]
      -- rw [State.Over.ofStep, e.unprocessed₂_eq, hp, Set.insert_diff_self_of_not_mem u]
      sorry 

end Instantaneous

theorem AdvanceTag.of_nonterminal_closed {s : State.Over rtr} 
    (ht : ¬s.Terminal) (hc : s.Closed) : ∃ s' : State α, Nonempty (s ⇓- s') := by
  have ⟨g, hg⟩ := State.Terminal.not_elim ht |>.resolve_left (not_not.mpr hc)
  exact ⟨⟨clear s.rtr, g, ∅⟩, ⟨hc, ⟨hg, clear_cleared _⟩⟩⟩

-- A reactor has the progress property, if from any nonterminal state based at that reactor, we can 
-- perform an execution step.
def Progress [Practical α] (rtr : α) : Prop :=
  ∀ (s : State.Over rtr), ¬s.Terminal → (∃ s' : State α, s ⇓ s')    

namespace Progress

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

theorem of_deps_acyclic (a : Dependency.Acyclic rtr) : Progress rtr := by
  intro s ht
  if hc : s.Closed then 
    have ⟨_, ⟨a⟩⟩ := AdvanceTag.of_nonterminal_closed ht hc
    exact ⟨_, .advance a⟩
  else 
    have ⟨_, ⟨e⟩⟩ := Instantaneous.ClosedExecution.of_nonterminal_acyclic_not_closed ht a hc
    exact ⟨_, .close e⟩

theorem iff_deps_acyclic : (Progress rtr) ↔ (Dependency.Acyclic rtr) :=
  ⟨to_deps_acyclic, of_deps_acyclic⟩

end Progress
end Execution