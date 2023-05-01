import ReactorModel.Execution.Trace
import ReactorModel.Determinism.Execution

noncomputable section
open ReactorType Practical FiniteUpdatable Classical

-- TODO: Move the Determinism folder into the Execution folder.
--       Perhaps also rename it to Theorems, as it contains many lemmas which aren't only relevant
--       to proving determinism.

namespace ReactorType

variable [Practical α]

def refresh (rtr : α) (acts : ID ⇀ Value) (h : acts.Finite) : α :=
  update' (update' rtr .inp .absent) .out .absent -- TODO: Set the actions.

open FiniteUpdatable in
theorem refresh_correct (rtr : α) : Refresh rtr (refresh rtr acts h) acts where
  equiv := Equivalent.trans update'_equiv update'_equiv
  eq_state := by
    rw [refresh, update'_preserves (by simp : .stv ≠ .out), update'_preserves (by simp : .stv ≠ .inp)]
  acts := by
    -- rw [refresh, update'_preserves (by simp : .act ≠ .out), update'_preserves (by simp : .act ≠ .inp)]
    sorry
  inputs := by 
    rw [refresh, update'_preserves (by simp : .inp ≠ .out), update'_updated] 
  outputs := by 
    rw [refresh, update'_updated, update'_preserves (by simp : .out ≠ .inp)] 

end ReactorType

namespace Execution
namespace State

variable [Practical α]

def unprocessed (s : State α) : Set ID :=
  { i ∈ s.rtr[.rcn] | i ∉ s.progress }

protected structure Over (over : α) extends State α where 
  rtr_eq       : rtr = over := by rfl
  progress_sub : progress ⊆ rtr[.rcn].ids
  events_sub   : events.ids ⊆ rtr[.act].ids

namespace Over

variable {rtr rtr₁ : α} {s : State.Over rtr}

instance : CoeOut (State.Over rtr) (State α) where
  coe := State.Over.toState

theorem progress_finite (s : State.Over rtr) : s.progress.Finite :=
  Finite.fin s.rtr .rcn |>.subset s.progress_sub

theorem unprocessed_finite (s : State.Over rtr) : s.unprocessed.Finite := by
  simp [unprocessed, Set.setOf_and, s.rtr_eq]
  apply Set.Finite.inter_of_left $ Finite.fin rtr .rcn

theorem actions_finite (s : State.Over rtr) (g : Time.Tag) : (s.actions g).Finite := by 
  apply Set.Finite.subset (Finite.fin s.rtr .act)
  intro _ h
  simp [actions, bind] at h
  sorry

theorem unprocessed_empty_iff_closed : (s.unprocessed = ∅) ↔ s.Closed := by
  simp [unprocessed, Closed]
  constructor <;> (intro h₁; ext1 i; constructor) <;> intro h₂
  · exact s.progress_sub h₂
  · simp [Set.ext_iff, Partial.mem_def] at h₁; exact h₁ _ h₂
  · simp [h₁, Partial.mem_def] at h₂
  · contradiction   

theorem not_closed_to_nontrivial (h : ¬s.Closed) : s.Nontrivial := by
  by_contra hn
  have ht' := State.Trivial.of_not_nontrivial hn
  have hp := s.progress_sub
  simp [State.Closed, ht', Partial.empty_ids, Set.subset_empty_iff] at h hp
  contradiction

theorem progress_ssubset_of_not_closed (hc : ¬s.Closed) : s.progress ⊂ s.rtr[.rcn].ids :=
  Set.ssubset_iff_subset_ne.mpr ⟨s.progress_sub, hc⟩

theorem exists_unprocessed_of_not_closed (hc : ¬s.Closed) : ∃ i ∈ s.rtr[.rcn], i ∉ s.progress := by
  have ⟨i, _, _⟩ := Set.exists_of_ssubset $ s.progress_ssubset_of_not_closed hc
  exists i

theorem exists_allowed_of_acyclic_has_unprocessed 
    (a : Dependency.Acyclic rtr) (h₁ : i ∈ s.rtr[.rcn]) (h₂ : i ∉ s.progress) : ∃ i, s.Allows i :=
  if h : dependencies s.rtr i \ s.progress = ∅ then
    ⟨i, ‹_›, Set.diff_eq_empty.mp h, ‹_›⟩
  else
    have ⟨_, hd⟩ := Set.nonempty_iff_ne_empty.mpr h
    have ⟨h₁, h₂⟩ := Set.mem_diff _ |>.mp hd
    exists_allowed_of_acyclic_has_unprocessed a h₁.mem₁ h₂
termination_by exists_allowed_of_acyclic_has_unprocessed s i _ _ _ => 
  have fin := Set.Finite.diff (Finite.fin s.rtr .rcn |>.subset $ dependencies_subset _ i) s.progress
  fin.toFinset.card
decreasing_by
  simp_wf
  refine Finset.card_lt_card $ Set.Finite.toFinset_strictMono ?_
  have h := mem_dependencies_ssubset a $ s.rtr_eq ▸ h₁
  simp [ssubset_iff_subset_ne, s.rtr_eq] at h ⊢ 
  refine ⟨?subset, ?ne⟩
  case subset =>
    intro x hx
    simp [Set.mem_diff] at hx ⊢ 
    exact ⟨h.left hx.left, hx.right⟩
  case ne =>
    simp [Set.ext_iff]
    refine ⟨_, h₂, ?_⟩
    rw [iff_true_right $ s.rtr_eq ▸ h₁]
    exact a _

theorem exists_allowed_of_acyclic_not_closed (a : Dependency.Acyclic rtr) (hc : ¬s.Closed) : 
    ∃ i, s.Allows i :=
  have ⟨_, hi₁, hi₂⟩ := s.exists_unprocessed_of_not_closed hc
  exists_allowed_of_acyclic_has_unprocessed a hi₁ hi₂

def ofStep {s₁ : State.Over rtr₁} {s₂ : State α} (e : s₁ ⇓ᵢ s₂) : State.Over s₂.rtr := 
  { s₂ with 
    progress_sub := by 
      simp [e.progress_eq, ←Equivalent.obj?_rcn_eq e.equiv]
      exact Set.insert_subset.mpr ⟨e.allows_rcn.mem, s₁.progress_sub⟩ 
    events_sub := by
      sorry
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
  let ⟨rcn, ha⟩ := s.exists_allowed_of_acyclic_not_closed a hc
  if h : s.Triggers rcn
  then ⟨s.exec rcn |>.record rcn, ⟨.exec ha h⟩⟩
  else ⟨s.record rcn, ⟨.skip ha h⟩⟩  

theorem unprocessed_eq (e : s₁ ⇓ᵢ s₂) : s₂.unprocessed = s₁.unprocessed \ {e.rcn} := by
  ext i
  simp [State.unprocessed, Equivalent.obj?_rcn_eq e.equiv, and_assoc]
  intro _
  have h := e.mem_progress_iff (rcn' := i) |>.not
  push_neg at h
  simp [and_comm, h]

theorem rcn_mem_unprocessed (e : s₁ ⇓ᵢ s₂) : e.rcn ∈ s₁.unprocessed := 
  ⟨e.allows_rcn.mem, e.allows_rcn.unprocessed⟩ 

theorem unprocessed_ssubset (e : s₁ ⇓ᵢ s₂) : s₂.unprocessed ⊂ s₁.unprocessed := by
  simp [e.unprocessed_eq, Set.ssubset_iff_subset_ne]
  exact e.rcn_mem_unprocessed

end Step

theorem ClosedExecution.of_acyclic_not_closed {rtr : α} {s : State.Over rtr} 
    (a : Dependency.Acyclic rtr) (hc : ¬s.Closed) : ∃ s' : State α, Nonempty (s ⇓| s') :=
  have ⟨sₑ, ⟨e⟩⟩ := Instantaneous.Step.of_acyclic_not_closed a hc
  if hc' : sₑ.Closed then
    ⟨_, ⟨.single e, hc'⟩⟩ 
  else
    have a' := Dependency.Acyclic.equiv e.equiv (s.rtr_eq.symm ▸ a)
    have ⟨_, ⟨e'⟩⟩ := of_acyclic_not_closed (s := s.ofStep e) a' hc'
    ⟨_, ⟨.trans e e'.exec, e'.closed⟩⟩   
termination_by of_acyclic_not_closed s _ _ _ => s.unprocessed_finite.toFinset.card
decreasing_by
  simp_wf
  exact Finset.card_lt_card $ Set.Finite.toFinset_strictMono $ e.unprocessed_ssubset

end Instantaneous

theorem Advance.of_nonterminal_closed {s : State.Over rtr} 
    (ht : ¬s.Terminal) (hc : s.Closed) : ∃ s' : State α, s ⇓- s' := by
  have ⟨g, hg⟩ := State.Terminal.not_elim ht |>.resolve_left (not_not.mpr hc)
  exists ⟨refresh s.rtr (s.actions g) $ s.actions_finite g, g, ∅, s.events⟩
  exact ⟨hc, hg, refresh_correct _⟩

-- A reactor has the progress property, if from any nonterminal state based at that reactor, we can 
-- perform an execution step.
def Progress [Practical α] (rtr : α) : Prop :=
  ∀ (s : State.Over rtr), ¬s.Terminal → (∃ s' : State α, s ⇓ s')    

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