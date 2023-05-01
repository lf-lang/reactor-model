import ReactorModel.Determinism.State

open Classical ReactorType Practical

namespace Execution
namespace Instantaneous
namespace Step

variable [Practical α] {s₁ s₂ : State α} in section
  
theorem mem_progress_iff (e : s₁ ⇓ᵢ s₂) : rcn' ∈ s₂.progress ↔ rcn' = e.rcn ∨ rcn' ∈ s₁.progress := 
  by cases e <;> simp [State.mem_record_progress_iff, rcn, State.exec_preserves_progress]

-- Corollary of `InstStep.mem_progress_iff`.
theorem progress_monotonic (e : s₁ ⇓ᵢ s₂) (h : rcn' ∈ s₁.progress) : rcn' ∈ s₂.progress := 
  e.mem_progress_iff.mpr $ .inr h

-- Corollary of `InstStep.mem_progress_iff`.
theorem rcn_mem_progress : (e : s₁ ⇓ᵢ s₂) → e.rcn ∈ s₂.progress := 
  (·.mem_progress_iff.mpr $ .inl rfl)

theorem rcn_not_mem_progress (e : s₁ ⇓ᵢ s₂) : e.rcn ∉ s₁.progress := 
  e.allows_rcn.unprocessed

theorem not_closed (e : s₁ ⇓ᵢ s₂) : ¬s₁.Closed :=
  (· ▸ e.allows_rcn.unprocessed $ e.allows_rcn.mem)

theorem preserves_tag : (s₁ ⇓ᵢ s₂) → s₁.tag = s₂.tag 
  | skip .. | exec .. => by simp [State.record_preserves_tag, State.exec_preserves_tag]

theorem equiv : (s₁ ⇓ᵢ s₂) → s₁.rtr ≈ s₂.rtr
  | skip .. => .refl _
  | exec .. => s₁.exec_equiv _

theorem deterministic (e₁ : s ⇓ᵢ s₁) (e₂ : s ⇓ᵢ s₂) (h : e₁.rcn = e₂.rcn) : s₁ = s₂ := by
  cases e₁ <;> cases e₂
  all_goals simp [rcn] at h; subst h; first | rfl | contradiction

theorem acyclic (e : s₁ ⇓ᵢ s₂) : e.rcn ≮[s₁.rtr] e.rcn :=
  e.allows_rcn.acyclic

theorem progress_eq : (e : s₁ ⇓ᵢ s₂) → s₂.progress = s₁.progress.insert e.rcn
  | skip .. | exec .. => by simp [State.exec_preserves_progress, State.record]; rfl

theorem progress_ssubset (e : s₁ ⇓ᵢ s₂) : s₁.progress ⊂ s₂.progress := by
  simp [e.progress_eq, Set.ssubset_iff_insert]
  exists e.rcn, e.allows_rcn.unprocessed

theorem seq_wellordered (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) : e₂.rcn ≮[s₁.rtr] e₁.rcn := by
  by_contra d
  exact e₂.allows_rcn.unprocessed $ e₁.progress_monotonic $ e₁.allows_rcn.deps d

theorem seq_rcn_ne (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) : e₁.rcn ≠ e₂.rcn := by
  by_contra he
  exact e₂.allows_rcn.unprocessed (he ▸ e₁.rcn_mem_progress)

end

variable [Practical α] {s₁ s₂ s₃ : State α}

theorem prepend_indep' (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (s₃' : _) (e₁' : s₁ ⇓ᵢ s₂') (e₂' : s₂' ⇓ᵢ s₃'), 
      (e₁'.rcn = e₂.rcn) ∧ (e₂'.rcn = e₁.rcn) ∧ (s₃' = s₃) := by
  have hi : _ ≮[_]≯ _ := { not_eq := e₁.seq_rcn_ne e₂, left := h, right := e₁.seq_wellordered e₂ }
  cases e₁ <;> cases e₂ <;> simp [rcn] at hi  
  case skip.skip ha₁ ht₁ rcn₂ ha₂ ht₂ =>
    have ha₁' := State.record_indep_allows_iff hi.symm |>.mp ha₁
    have ha₂' := State.record_indep_allows_iff hi |>.mpr ha₂
    have ht₁' := State.record_triggers_iff (i₁ := rcn₂) |>.not.mp ht₁
    have ht₂' := State.record_triggers_iff (i₂ := rcn₂) |>.not.mpr ht₂
    exact ⟨_, _, Step.skip ha₂' ht₂', Step.skip ha₁' ht₁', rfl, rfl, State.record_comm⟩
  case skip.exec ha₁ ht₁ _ ha₂ ht₂ =>
    have ha₁' := State.exec_record_indep_allows_iff hi |>.mp ha₁
    have ha₂' := State.record_indep_allows_iff hi |>.mpr ha₂
    have ht₁' := State.exec_record_indep_triggers_iff hi |>.not.mp ht₁
    have ht₂' := State.record_triggers_iff.mpr ht₂
    refine ⟨_, _, Step.exec ha₂' ht₂', Step.skip ha₁' ht₁', rfl, rfl, ?_⟩
    simp [rcn, State.record_exec_comm, State.record_comm]
  case exec.skip ha₁ ht₁ rcn₂ ha₂ ht₂ => 
    have ha₁' := State.record_indep_allows_iff hi.symm |>.mp ha₁
    have ha₂' := State.exec_record_indep_allows_iff hi.symm |>.mpr ha₂
    have ht₁' := State.record_triggers_iff (i₁ := rcn₂) |>.mp ht₁
    have ht₂' := State.exec_record_indep_triggers_iff hi.symm |>.not.mpr ht₂
    refine ⟨_, _, Step.skip ha₂' ht₂', Step.exec ha₁' ht₁', rfl, rfl, ?_⟩
    simp [rcn, State.record_exec_comm, State.record_comm]
  case exec.exec ha₁ ht₁ _ ha₂ ht₂ =>
    have ha₁' := State.exec_record_indep_allows_iff hi |>.mp ha₁
    have ha₂' := State.exec_record_indep_allows_iff hi.symm |>.mpr ha₂
    have ht₁' := State.exec_record_indep_triggers_iff hi |>.mp ht₁
    have ht₂' := State.exec_record_indep_triggers_iff hi.symm |>.mpr ht₂
    refine ⟨_, _, Step.exec ha₂' ht₂', Step.exec ha₁' ht₁', rfl, rfl, ?_⟩
    simp [rcn, State.record_exec_comm, State.record_comm, State.exec_indep_comm hi]

theorem prepend_indep (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (e₁' : s₁ ⇓ᵢ s₂') (e₂' : s₂' ⇓ᵢ s₃), (e₁'.rcn = e₂.rcn) ∧ (e₂'.rcn = e₁.rcn) := by
  have ⟨s₂', _, e₁', e₂', h₁, h₂, h⟩ := prepend_indep' e₁ e₂ h
  subst h
  exists s₂', e₁', e₂'

end Step
end Instantaneous 
end Execution