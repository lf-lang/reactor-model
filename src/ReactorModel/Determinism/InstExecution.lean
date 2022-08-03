import ReactorModel.Determinism.InstStep

open Classical

namespace Execution

theorem InstExecution.preserves_tag : (s₁ ⇓ᵢ+ s₂) → s₁.ctx.tag = s₂.ctx.tag
  | single h => h.preserves_tag
  | trans h hi => h.preserves_tag.trans hi.preserves_tag

theorem InstExecution.preserves_ctx_past_future {s₁ s₂} :
  (s₁ ⇓ᵢ+ s₂) → ∀ g, g ≠ s₁.ctx.tag → s₁.ctx.processedRcns g = s₂.ctx.processedRcns g := by
  intro h g hg
  induction h
  case single h => exact h.preserves_ctx_past_future _ hg
  case trans s₁ _ sₘ he _ hi =>
    rw [InstExecution.preserves_tag $ single he] at hg
    exact (he.preserves_ctx_past_future _ hg).trans $ hi hg
    
theorem InstExecution.preserves_rcns {i : ID} :
  (s₁ ⇓ᵢ+ s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i)
  | single h => h.preserves_rcns
  | trans h₁ₘ hₘ₂ => h₁ₘ.preserves_rcns.trans hₘ₂.preserves_rcns

theorem InstExecution.rcns_unprocessed : 
  (e : s₁ ⇓ᵢ+ s₂) → ∀ rcn ∈ e.rcns, rcn ∉ s₁.ctx.currentProcessedRcns := by
  intro h rcn hr
  induction h
  case single h => simp [List.mem_singleton.mp hr, h.rcn_unprocessed]
  case trans hi =>
    cases List.mem_cons.mp hr
    case inl h _ hc => simp [hc, h.rcn_unprocessed]
    case inr h₁ _ h => 
      specialize hi h
      exact ((not_or _ _).mp $ (mt h₁.mem_currentProcessedRcns.mpr) hi).right

theorem InstExecution.rcns_nodup : (e : s₁ ⇓ᵢ+ s₂) → List.Nodup e.rcns
  | single _ => List.nodup_singleton _
  | trans h₁ h₂ => List.nodup_cons.mpr $ ⟨(mt $ h₂.rcns_unprocessed _) $ not_not.mpr h₁.self_currentProcessedRcns, h₂.rcns_nodup⟩

theorem InstExecution.currentProcessedRcns_monotonic :
  (s₁ ⇓ᵢ+ s₂) → s₁.ctx.currentProcessedRcns ⊆ s₂.ctx.currentProcessedRcns := by
  intro h
  apply Finset.subset_iff.mpr
  intro rcn hr
  induction h
  case single h => exact h.monotonic_currentProcessedRcns hr
  case trans h _ hi => exact hi $ h.monotonic_currentProcessedRcns hr

theorem InstExecution.mem_currentProcessedRcns :
  (e : s₁ ⇓ᵢ+ s₂) → ∀ rcn, rcn ∈ s₂.ctx.currentProcessedRcns ↔ rcn ∈ e.rcns ∨ rcn ∈ s₁.ctx.currentProcessedRcns := by
  intro h rcn
  induction h
  case single h => simp [rcns, List.mem_singleton, h.mem_currentProcessedRcns]
  case trans h₁ h₂ hi => 
    constructor <;> intro hc 
    case mp =>
      cases hi.mp hc with
      | inl h => exact .inl $ List.mem_cons_of_mem _ h
      | inr h => 
        by_cases hc : rcn ∈ (h₁.rcn :: h₂.rcns)
        case pos => exact .inl hc
        case neg => exact .inr $ (h₁.mem_currentProcessedRcns.mp h).resolve_left $ List.ne_of_not_mem_cons hc
    case mpr =>
      cases hc with
      | inl h => 
        cases (List.mem_cons_iff ..).mp h with
        | inl h => exact hi.mpr $ .inr (h ▸ h₁.self_currentProcessedRcns)
        | inr h => exact hi.mpr $ .inl h
      | inr h => exact hi.mpr $ .inr $ h₁.monotonic_currentProcessedRcns h

-- Corollary of `InstExecution.mem_currentProcessedRcns`.
theorem InstExecution.self_currentProcessedRcns : 
  (e : s₁ ⇓ᵢ+ s₂) → ∀ rcn ∈ e.rcns, rcn ∈ s₂.ctx.currentProcessedRcns := 
  λ h _ hm => (h.mem_currentProcessedRcns _).mpr $ .inl hm
  
theorem InstExecution.eq_ctx_processed_rcns_perm : 
  (e₁ : s ⇓ᵢ+ s₁) → (e₂ : s ⇓ᵢ+ s₂) → (s₁.ctx = s₂.ctx) → e₁.rcns ~ e₂.rcns := by
  intro h₁ h₂ he
  apply (List.perm_ext h₁.rcns_nodup h₂.rcns_nodup).mpr
  intro rcn
  by_cases hc : rcn ∈ s.ctx.currentProcessedRcns
  case pos =>
    have h₁ := (mt $ h₁.rcns_unprocessed rcn) (not_not.mpr hc)
    have h₂ := (mt $ h₂.rcns_unprocessed rcn) (not_not.mpr hc)
    exact iff_of_false h₁ h₂ 
  case neg =>
    constructor <;> intro hm
    case mp => 
      have h := h₁.self_currentProcessedRcns _ hm
      rw [he] at h
      exact ((h₂.mem_currentProcessedRcns _).mp h).resolve_right hc
    case mpr =>
      have h := h₂.self_currentProcessedRcns _ hm
      rw [←he] at h
      exact ((h₁.mem_currentProcessedRcns _).mp h).resolve_right hc

theorem InstExecution.rcns_respect_dependencies : 
  (e : s₁ ⇓ᵢ+ s₂) →
  e.rcns.get? i₁ = some rcn₁ → e.rcns.get? i₂ = some rcn₂ → 
  rcn₁ >[s₁.rtr] rcn₂ → i₁ < i₂ := by
  intro h h₁ h₂ hd
  sorry

theorem InstExecution.rcn_list_cons : (e : s₁ ⇓ᵢ+ s₂) → ∃ hd tl, e.rcns = hd :: tl :=
  (by cases · <;> simp [rcns])

theorem InstExecution.to_ChangeListStep :
  (e : s₁ ⇓ᵢ+ s₂) → (s₁ -[e.changes]→* ⟨s₂.rtr, s₁.ctx⟩) := by
  intro e
  induction e
  case single e => simp [changes, e.to_ChangeListStep]
  case trans s₁ sₘ s₂ e₁ e₂ hi => 
    have h := e₁.to_ChangeListStep
    simp [changes]
    have hs := ChangeListStep.append h hi rfl
    exact hs
  
-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
protected theorem InstExecution.deterministic : 
  (s ⇓ᵢ+ s₁) → (s ⇓ᵢ+ s₂) → (s₁.ctx = s₂.ctx) → s₁ = s₂ := by
  intro h₁ h₂ hc
  refine State.ext _ _ ?_ hc
  have hp := h₁.eq_ctx_processed_rcns_perm h₂ hc
  suffices h : h₁.changes ⋈ h₂.changes by 
    injection h₁.to_ChangeListStep.equiv_changes_eq_result h₂.to_ChangeListStep h
    assumption
  sorry
    
    
      