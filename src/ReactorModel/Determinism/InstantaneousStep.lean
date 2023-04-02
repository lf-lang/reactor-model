import ReactorModel.Determinism.State

open Classical ReactorType Indexable

namespace Execution
namespace Instantaneous
namespace Step

variable [Indexable α] {s₁ s₂ : State α}

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

/-
theorem Skip.equiv : (s₁ ⇓ₛ s₂) → s₁.rtr ≈ s₂.rtr
  | mk .. => .refl

theorem Skip.progress_eq : (e : s₁ ⇓ₛ s₂) → s₂.progress = s₁.progress.insert e.rcn
  | mk .. => rfl

theorem Skip.progress_mono (e : s₁ ⇓ₛ s₂) : s₁.progress ⊆ s₂.progress := by
  simp [e.progress_eq]
  apply Set.subset_insert

theorem Skip.triggers_iff (e : s₁ ⇓ₛ s₂) : (s₁.Triggers i) ↔ (s₂.Triggers i) := by 
  cases e
  case mk rcn _ _ =>
    constructor
    all_goals
      intro h
      sorry -- exact h.progress_agnostic (s₁.record_preserves_rtr rcn) (s₁.record_preserves_tag rcn) |>.choose_spec

theorem Skip.mem_progress_iff (e : s₁ ⇓ₛ s₂) : 
    (rcn' ∈ s₂.progress) ↔ (rcn' = e.rcn ∨ rcn' ∈ s₁.progress) := by
  sorry

theorem Skip.preserves_allows_indep (e₁ : s₁ ⇓ₛ s₂) (e₂ : s₂ ⇓ₛ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) : 
    s₁.Allows e₂.rcn where
  mem := sorry
  unprocessed := Set.not_mem_subset e₁.progress_mono $ e₂.allows_rcn.unprocessed
  deps := by
    intro i hi
    have h' := equiv_eq_dependencies e₁.equiv |>.symm ▸ e₂.allows_rcn.deps
    refine e₁.mem_progress_iff.mp (h' hi) |>.resolve_left ?_
    intro hc; subst hc; contradiction

set_option pp.proofs.withType false
theorem Skip.swap_indep_skip (e₁ : s₁ ⇓ₛ s₂) (e₂ : s₂ ⇓ₛ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) : 
    ∃ (s₂' : _) (f₁ : s₁ ⇓ₛ s₂') (f₂ : s₂' ⇓ₛ s₃), (f₁.rcn = e₂.rcn) ∧ (f₂.rcn = e₁.rcn) := by 
  have ha := e₁.preserves_allows_indep e₂ h
  have ht := e₁.triggers_iff.not.mpr e₂.not_triggers
  have e₁' := Skip.mk ha ht
  simp at e₁'
  exists _, e₁'
  sorry -- TODO: This is super annoying. Is there a better way to approach this?
        --       Do we need more preservation theorems for `Allows` and `Triggers` first?

theorem Skip.swap_indep_exec (e₁ : s₁ ⇓ₛ s₂) (e₂ : s₂ ⇓ₑ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) : 
    ∃ (s₂' : _) (f₁ : s₁ ⇓ₑ s₂') (f₂ : s₂' ⇓ₛ s₃), (f₁.rcn = e₂.rcn) ∧ (f₂.rcn = e₁.rcn) := by 
  sorry

theorem Skip.swap_indep (e₁ : s₁ ⇓ₛ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) : 
    ∃ (s₂' : _) (f₁ : s₁ ⇓ᵢ s₂') (f₂ : s₂' ⇓ₛ s₃), (f₁.rcn = e₂.rcn) ∧ (f₂.rcn = e₁.rcn) := by 
  cases e₂
  case skip e₂ =>
    have ⟨_, e₁', e₂', _⟩ := e₁.swap_indep_skip e₂ h
    exists _, skip e₁', e₂'
  case exec e₂ =>
    have ⟨_, e₁', e₂', _⟩ := e₁.swap_indep_exec e₂ h
    exists _, exec e₁', e₂'

theorem Exec.equiv : (s₁ ⇓ₑ s₂) → s₁.rtr ≈ s₂.rtr
  | mk .. => by simp [State.record_preserves_rtr, s₁.exec_equiv]

theorem Exec.progress_eq : (e : s₁ ⇓ₑ s₂) → s₂.progress = s₁.progress.insert e.rcn
  | mk .. => rfl
-/

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

theorem prepend_indep' (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (s₃' : _) (e₁' : s₁ ⇓ᵢ s₂') (e₂' : s₂' ⇓ᵢ s₃'), 
      (e₁'.rcn = e₂.rcn) ∧ (e₂'.rcn = e₁.rcn) ∧ (s₃' = s₃) := by
  have hi : _ ≮[_]≯ _ := { not_eq := e₁.seq_rcn_ne e₂, left := h, right := e₁.seq_wellordered e₂ }
  cases e₁ <;> cases e₂ 
  case skip.skip => sorry
  case skip.exec => sorry
  case exec.skip => sorry
  case exec.exec rcn₁ ha₁ ht₁ rcn₂ ha₂ ht₂ =>
    have ha₁' : (s₁.exec rcn₂ |>.record rcn₂).Allows rcn₁ := sorry
    have ht₁' : (s₁.exec rcn₂ |>.record rcn₂).Triggers rcn₁ := sorry
    have ha₂' : s₁.Allows rcn₂ := sorry
    have ht₂' : s₁.Triggers rcn₂ := sorry
    refine ⟨_, _, Step.exec ha₂' ht₂', Step.exec ha₁' ht₁', rfl, rfl, ?_⟩
    sorry -- by ext

theorem prepend_indep (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (e₁' : s₁ ⇓ᵢ s₂') (e₂' : s₂' ⇓ᵢ s₃), (e₁'.rcn = e₂.rcn) ∧ (e₂'.rcn = e₁.rcn) := by
  have ⟨s₂', _, e₁', e₂', h₁, h₂, h⟩ := prepend_indep' e₁ e₂ h
  subst h
  exists s₂', e₁', e₂'

end Step
end Instantaneous 
end Execution