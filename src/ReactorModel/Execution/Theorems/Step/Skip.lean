import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.State

open Classical Reactor Execution State

namespace Execution.Step.Skip

variable [Hierarchical α] {s₁ : State α}

def rcn :                      (s₁ ↓ˢ s₂) → ID                                | mk (rcn := rcn) .. => rcn
def clock :                    (s₁ ↓ˢ s₂) → _root_.Time                       | mk (t := t) .. => t
theorem allows_rcn :       (e : s₁ ↓ˢ s₂) → Allows s₁ e.rcn                   | mk a .. => a
theorem not_triggers_rcn : (e : s₁ ↓ˢ s₂) → ¬Triggers s₁ e.rcn                | mk _ t _ => t
theorem clock_le :         (e : s₁ ↓ˢ s₂) → s₁.clock ≤ e.clock                | mk _ _ c => c
theorem dst_eq :           (e : s₁ ↓ˢ s₂) → s₂ = (s₁.at e.clock).record e.rcn | mk .. => rfl

theorem preserves_rtr (e : s₁ ↓ˢ s₂) : s₁.rtr = s₂.rtr := by
  simp [e.dst_eq, record_preserves_rtr, at_preserves_rtr]

theorem preserves_tag (e : s₁ ↓ˢ s₂) : s₁.tag = s₂.tag := by
  simp [e.dst_eq, record_preserves_tag, at_preserves_tag]

theorem preserves_events (e : s₁ ↓ˢ s₂) : s₁.events = s₂.events := by
  simp [e.dst_eq, record_preserves_events, at_preserves_events]

theorem equiv (e : s₁ ↓ˢ s₂) : s₁.rtr ≈ s₂.rtr := by
  simp [e.dst_eq, record_preserves_rtr, at_preserves_rtr]
  exact .refl _

theorem progress_eq (e : s₁ ↓ˢ s₂) : s₂.progress = s₁.progress.insert e.rcn := by 
  simp [e.dst_eq, at_preserves_progress, record_progress_eq]

theorem preserves_nontrivial {e : s₁ ↓ˢ s₂} (n : s₁.Nontrivial) : s₂.Nontrivial :=
  n.equiv e.equiv

theorem indep_allows_iff (e : s₁ ↓ˢ s₂) (hi : i ≮[s₁.rtr]≯ e.rcn) : 
    s₁.Allows i ↔ s₂.Allows i := by
  simp [e.dst_eq, Allows.iff_record_indep hi.symm, Allows.iff_at (s := s₁.record _) (t := e.clock)]
  rfl

theorem triggers_iff (e : s₁ ↓ˢ s₂) : s₁.Triggers i ↔ s₂.Triggers i := by
  simp [
    e.dst_eq, Triggers.iff_record (s := s₁) (i₁ := e.rcn), 
    Triggers.iff_at (s := s₁.record _) (t := e.clock)
  ]
  rfl

theorem comm 
    (e₁ : s ↓ˢ s₁) (e₁₂ : s₁ ↓ˢ s₁₂) (e₂ : s ↓ˢ s₂) (e₂₁ : s₂ ↓ˢ s₂₁) (hr₁ : e₁.rcn = e₂₁.rcn) 
    (hr₂ : e₂.rcn = e₁₂.rcn) : s₁₂ ≈ s₂₁ := by 
  constructor
  case rtr => 
    exact e₁₂.preserves_rtr ▸ e₁.preserves_rtr ▸ e₂₁.preserves_rtr ▸ e₂.preserves_rtr 
  case tag => 
    exact e₁₂.preserves_tag ▸ e₁.preserves_tag ▸ e₂₁.preserves_tag ▸ e₂.preserves_tag
  case events => 
    exact e₁₂.preserves_events ▸ e₁.preserves_events ▸ e₂₁.preserves_events ▸ e₂.preserves_events
  case progress  =>
    have h₁ := e₁.progress_eq ▸ e₁₂.progress_eq
    have h₂ := e₂.progress_eq ▸ e₂₁.progress_eq
    rw [hr₁, hr₂] at *
    simp [h₁, h₂]
    apply Set.insert_comm

theorem unprocessed_eq (e : s₁ ↓ˢ s₂) : s₂.unprocessed = s₁.unprocessed \ {e.rcn} := by
  ext i
  simp [State.unprocessed, Equivalent.obj?_rcn_eq e.equiv, and_assoc, e.progress_eq]
  intro _; simp [Set.insert]; push_neg; simp [and_comm]

theorem rcn_mem_unprocessed (e : s₁ ↓ˢ s₂) : e.rcn ∈ s₁.unprocessed := 
  ⟨e.allows_rcn.mem, e.allows_rcn.unprocessed⟩ 

theorem unprocessed_ssubset (e : s₁ ↓ˢ s₂) : s₂.unprocessed ⊂ s₁.unprocessed := by
  simp [e.unprocessed_eq, Set.ssubset_iff_subset_ne]
  exact e.rcn_mem_unprocessed

end Execution.Step.Skip