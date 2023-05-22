import ReactorModel.Execution.Theorems.State
import ReactorModel.Execution.Theorems.Trivial

noncomputable section
open Reactor Classical

namespace Execution.State.Over

variable [Proper α] [Reactor.Finite α]{rtr rtr₁ : α} {s : State.Over rtr}

theorem exists_allowed_of_acyclic_has_unprocessed 
    (a : Dependency.Acyclic rtr) (h₁ : i ∈ s.rtr[.rcn]) (h₂ : i ∉ s.progress) : ∃ i, s.Allows i :=
  if h : dependencies s.rtr i \ s.progress = ∅ then
    ⟨i, ‹_›, Set.diff_eq_empty.mp h, ‹_›⟩
  else
    have ⟨_, hd⟩ := Set.nonempty_iff_ne_empty.mpr h
    have ⟨h₁, h₂⟩ := Set.mem_diff _ |>.mp hd
    have := inferInstanceAs $ Reactor.Finite α
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

theorem progress_ssubset_of_not_closed (hc : ¬s.Closed) : s.progress ⊂ s.rtr[.rcn].ids :=
  Set.ssubset_iff_subset_ne.mpr ⟨s.progress_sub, hc⟩

theorem exists_unprocessed_of_not_closed (hc : ¬s.Closed) : ∃ i ∈ s.rtr[.rcn], i ∉ s.progress := by
  have ⟨i, _, _⟩ := Set.exists_of_ssubset $ s.progress_ssubset_of_not_closed hc
  exists i 

-- TODO: separate proof and definitions here
def allowed (a : Dependency.Acyclic rtr) (hc : ¬s.Closed) : { i : ID // s.Allows i } :=
  -- have ⟨_, hi₁, hi₂⟩ := s.exists_unprocessed_of_not_closed hc
  sorry -- exists_allowed_of_acyclic_has_unprocessed a hi₁ hi₂

def ofStep {s₁ : State.Over rtr₁} {s₂ : State α} (e : s₁ ↓ s₂) : State.Over s₂.rtr := 
  { s₂ with 
    progress_sub := by 
      sorry
      -- simp [e.progress_eq, ←Equivalent.obj?_rcn_eq e.equiv]
      -- exact Set.insert_subset.mpr ⟨e.allows_rcn.mem, s₁.progress_sub⟩ 
    events_sub := by
      sorry
  }

end Execution.State.Over