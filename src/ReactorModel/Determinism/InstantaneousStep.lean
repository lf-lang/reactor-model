import ReactorModel.Determinism.State

open Classical ReactorType Indexable

namespace Execution
namespace Instantaneous
namespace Step

variable [Indexable α] {s₁ s₂ : State α} in section

theorem rcn_not_mem_progress (e : s₁ ⇓ᵢ s₂) : e.rcn ∉ s₁.progress := 
  sorry -- e.allows.unprocessed

theorem preserves_tag (e : s₁ ⇓ᵢ s₂) : s₁.tag = s₂.tag := 
  sorry -- e.exec.preserves_tag
  
theorem mem_progress_iff :
  (e : s₁ ⇓ᵢ s₂) → (rcn' ∈ s₂.progress ↔ rcn' = e.rcn ∨ rcn' ∈ s₁.progress) := by
  intro h
  constructor
  case mp =>
    intro ho
    by_cases hc : rcn' = h.rcn
    case pos => exact .inl hc
    case neg => sorry
      -- rw [State.progress, h.exec.ctx_adds_rcn, ←rcn] at ho
      -- simp [Context.mem_record_progress_iff _ _ _ |>.mp ho]
  case mpr =>
    intro ho
    by_cases hc : rcn' = h.rcn
    case pos =>
      simp [hc]
      sorry
      -- exact Context.mem_record_progress_iff _ _ _ |>.mpr (.inl rfl)
    case neg =>
      sorry
      -- simp [State.progress, h.exec.ctx_adds_rcn, Context.mem_record_progress_iff _ _ _ |>.mpr (.inr $ ho.resolve_left hc)]

-- Corollary of `InstStep.mem_progress_iff`.
theorem not_mem_progress :
  (e : s₁ ⇓ᵢ s₂) → (rcn' ≠ e.rcn) → rcn' ∉ s₁.progress → rcn' ∉ s₂.progress := 
  sorry -- λ h hn hm => (mt h.mem_progress.mp) $ not_or.mpr ⟨hn, hm⟩

-- Corollary of `InstStep.mem_progress`.
theorem monotonic_progress : (s₁ ⇓ᵢ s₂) → rcn' ∈ s₁.progress → rcn' ∈ s₂.progress := 
  sorry -- (·.mem_progress_iff.mpr $ .inr ·)

-- Corollary of `InstStep.mem_progress`.
theorem rcn_mem_progress : (e : s₁ ⇓ᵢ s₂) → e.rcn ∈ s₂.progress := 
  (·.mem_progress_iff.mpr $ .inl rfl)

theorem not_Closed (e : s₁ ⇓ᵢ s₂) : ¬s₁.Closed := by
  intro c
  have h := c ▸ e.allows_rcn.unprocessed
  simp [Partial.mem_iff] at h 
  sorry -- have := h e.allows.mem.choose
  -- contradiction 

theorem equiv : (s₁ ⇓ᵢ s₂) → s₁.rtr ≈ s₂.rtr :=
  sorry

theorem deterministic (e₁ : s ⇓ᵢ s₁) (e₂ : s ⇓ᵢ s₂) (h : e₁.rcn = e₂.rcn) : s₁ = s₂ := by
  cases e₁ <;> cases e₂
  all_goals simp [rcn] at h; subst h; first | rfl | contradiction

theorem acyclic (e : s₁ ⇓ᵢ s₂) : e.rcn ≮[s₁.rtr] e.rcn :=
  e.allows_rcn.acyclic

theorem progress_eq : (e : s₁ ⇓ᵢ s₂) → s₂.progress = s₁.progress.insert e.rcn
  | skip .. | exec .. => rfl

theorem seq_wellordered (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) : e₂.rcn ≮[s₁.rtr] e₁.rcn := by
  by_contra d
  exact e₂.allows_rcn.unprocessed $ e₁.monotonic_progress $ e₁.allows_rcn.deps d

theorem seq_rcn_ne (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) : e₁.rcn ≠ e₂.rcn := by
  by_contra he
  exact e₂.allows_rcn.unprocessed (he ▸ e₁.rcn_mem_progress)

end

variable [Proper α] {s₁ s₂ s₃ : State α}

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
    simp [rcn, State.record_exec_comm, State.record_comm, State.exec_indep_comm hi.symm]

theorem prepend_indep (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (e₁' : s₁ ⇓ᵢ s₂') (e₂' : s₂' ⇓ᵢ s₃), (e₁'.rcn = e₂.rcn) ∧ (e₂'.rcn = e₁.rcn) := by
  have ⟨s₂', _, e₁', e₂', h₁, h₂, h⟩ := prepend_indep' e₁ e₂ h
  subst h
  exists s₂', e₁', e₂'

end Step
end Instantaneous 
end Execution