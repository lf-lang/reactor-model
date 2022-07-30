import ReactorModel.Determinism.InstStep

open Classical

namespace Execution

theorem InstExecution.preserves_tag : (s₁ ⇓ᵢ+[rcns] s₂) → s₁.ctx.tag = s₂.ctx.tag
  | single h => h.preserves_tag
  | trans h hi => h.preserves_tag.trans hi.preserves_tag

theorem InstExecution.preserves_ctx_past_future {s₁ s₂ rcns} :
  (s₁ ⇓ᵢ+[rcns] s₂) → ∀ g, g ≠ s₁.ctx.tag → s₁.ctx.processedRcns g = s₂.ctx.processedRcns g := by
  intro h g hg
  induction h
  case single h => exact h.preserves_ctx_past_future _ hg
  case trans s₁ _ sₘ he _ hi =>
    rw [InstExecution.preserves_tag $ single he] at hg
    exact (he.preserves_ctx_past_future _ hg).trans $ hi hg
    
theorem InstExecution.preserves_rcns {i : ID} :
  (s₁ ⇓ᵢ+[rcns] s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i)
  | single h => h.preserves_rcns
  | trans h₁ₘ hₘ₂ => h₁ₘ.preserves_rcns.trans hₘ₂.preserves_rcns

theorem InstExecution.rcns_unprocessed : 
  (s₁ ⇓ᵢ+[rcns] s₂) → ∀ rcn ∈ rcns, rcn ∉ s₁.ctx.currentProcessedRcns := by
  intro h rcn hr
  induction h
  case single h => simp [List.mem_singleton.mp hr, h.rcn_unprocessed]
  case trans hi =>
    cases List.mem_cons.mp hr
    case inl h _ hc => simp [hc, h.rcn_unprocessed]
    case inr h₁ _ h => 
      specialize hi h
      exact ((not_or _ _).mp $ (mt h₁.mem_currentProcessedRcns.mpr) hi).right

theorem InstExecution.rcns_nodup : (s₁ ⇓ᵢ+[rcns] s₂) → List.Nodup rcns
  | single _ => List.nodup_singleton _
  | trans h₁ h₂ => List.nodup_cons.mpr $ ⟨(mt $ h₂.rcns_unprocessed _) $ not_not.mpr h₁.self_currentProcessedRcns, h₂.rcns_nodup⟩

theorem InstExecution.currentProcessedRcns_monotonic :
  (s₁ ⇓ᵢ+[rcns] s₂) → s₁.ctx.currentProcessedRcns ⊆ s₂.ctx.currentProcessedRcns := by
  intro h
  apply Finset.subset_iff.mpr
  intro rcn hr
  induction h
  case single h => exact h.monotonic_currentProcessedRcns hr
  case trans h _ hi => exact hi $ h.monotonic_currentProcessedRcns hr

theorem InstExecution.mem_currentProcessedRcns :
  (s₁ ⇓ᵢ+[rcns] s₂) → ∀ rcn, rcn ∈ s₂.ctx.currentProcessedRcns ↔ rcn ∈ rcns ∨ rcn ∈ s₁.ctx.currentProcessedRcns := by
  intro h rcn
  induction h
  case single h => simp [List.mem_singleton, h.mem_currentProcessedRcns]
  case trans hd _ tl _ h₁ _ hi => 
    constructor <;> intro hc 
    case mp =>
      cases hi.mp hc with
      | inl h => exact .inl $ List.mem_cons_of_mem _ h
      | inr h => 
        by_cases hc : rcn ∈ (hd::tl)
        case pos => exact .inl hc
        case neg => exact .inr $ (h₁.mem_currentProcessedRcns.mp h).resolve_left $ List.ne_of_not_mem_cons hc
    case mpr =>
      cases hc with
      | inl h => 
        cases (List.mem_cons_iff ..).mp h with
        | inl h => rw [←h] at h₁; exact hi.mpr $ .inr h₁.self_currentProcessedRcns
        | inr h => exact hi.mpr $ .inl h
      | inr h => exact hi.mpr $ .inr $ h₁.monotonic_currentProcessedRcns h

-- Corollary of `InstExecution.mem_currentProcessedRcns`.
theorem InstExecution.self_currentProcessedRcns : 
  (s₁ ⇓ᵢ+[rcns] s₂) → ∀ rcn ∈ rcns, rcn ∈ s₂.ctx.currentProcessedRcns := 
  λ h _ hm => (h.mem_currentProcessedRcns _).mpr $ .inl hm
  
theorem InstExecution.eq_ctx_processed_rcns_perm : 
  (s ⇓ᵢ+[rcns₁] s₁) → (s ⇓ᵢ+[rcns₂] s₂) → (s₁.ctx = s₂.ctx) → rcns₁ ~ rcns₂ := by
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
  (s₁ ⇓ᵢ+[rcns] s₂) →
  rcns.get? i₁ = some rcn₁ → rcns.get? i₂ = some rcn₂ → 
  rcn₁ >[s₁.rtr] rcn₂ → i₁ < i₂ := by
  intro h h₁ h₂ hd
  sorry

theorem InstExecution.rcn_list_cons : (s₁ ⇓ᵢ+[rcns] s₂) → ∃ hd tl, rcns = hd :: tl :=
  (by cases · <;> simp)

-- A Given list of change segments is well-formed over a given instantaneous execution,
-- if each set of changes corresponds to the output of the reaction at the same position. 
inductive InstExecution.Changes.WFSegments : (s₁ ⇓ᵢ+[rcns] s₂) → List (List Change) → Prop
  | singleSkip (e : s₁ ⇓ᵢ[rcn] s₂) : (s₁.rcnOutput rcn = none)    → WFSegments (.single e) [[]]
  | singleExec (e : s₁ ⇓ᵢ[rcn] s₂) : (s₁.rcnOutput rcn = some cs) → WFSegments (.single e) [cs]
  | transSkip (e₁ : s₁ ⇓ᵢ[hd] s') {e₂ : s' ⇓ᵢ+[tl] s₂} : (s₁.rcnOutput hd = none) → (WFSegments e₂ ctl) → WFSegments (.trans e₁ e₂) ctl
  | transExec (e₁ : s₁ ⇓ᵢ[hd] s') {e₂ : s' ⇓ᵢ+[tl] s₂} : (s₁.rcnOutput hd = some chd) → (WFSegments e₂ ctl) → WFSegments (.trans e₁ e₂) ([chd] ++ ctl)

-- This structure flattens an instantaneous execution into a list of changes.
structure InstExecution.Changes (h : s₁ ⇓ᵢ+[rcns] s₂) where
  segments : List (List Change)
  endState : State
  wfExec : ∃ rcn, s₁ -[rcn:segments.join]→* endState -- The `∃ rcn` is kind of weird, but hopefully we'll remove the whole lifting of reactions into the execution relations at some point - then this can be dropped.
  wfEndState : s₂ = { endState with ctx := endState.ctx.addCurrentProcessed' rcns }
  wfSegments : Changes.WFSegments h segments

theorem InstExecution.Changes.intro : (h : s₁ ⇓ᵢ+[rcns] s₂) → Nonempty (InstExecution.Changes h) := by
  intro h
  induction h
  case single h =>
    have ⟨cs, s₂', _, h₁, h₂⟩ := h.changes
    refine Nonempty.intro ?_
    apply Changes.mk [cs] s₂'
    case wfExec => simp; exact ⟨_, h₁⟩
    case wfEndState => exact h₂
    case wfSegments =>
      cases H : h
      case execReaction =>
        apply Changes.WFSegments.singleExec h 
        sorry
      all_goals sorry
  case trans hd s₂ tl s₃ hhd htl hi =>
    -- have ⟨tlcs, tls₂', _, _⟩ := hi
    -- have ⟨hdcs, _, _, h₁, h₂⟩ := hhd.changes
    -- exists [hdcs] ++ tlcs
    sorry
    -- i think we can' prove the rest here because we're missing the execution contexts.
    -- figure out a nice way (perhaps a structure) to state the property that should be the result of this theorem.
    -- that would probably also help you with proving it.

-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
protected theorem InstExecution.deterministic : 
  (s ⇓ᵢ+[rcns₁] s₁) → (s ⇓ᵢ+[rcns₂] s₂) → (s₁.ctx = s₂.ctx) → s₁ = s₂ := by
  intro h₁ h₂ hc
  refine State.ext _ _ ?_ hc
  have hp := h₁.eq_ctx_processed_rcns_perm h₂ hc
  let cs₁ := Changes.intro h₁ |>.some
  let cs₂ := Changes.intro h₂ |>.some
  suffices h : cs₁.segments.join ⋈ cs₂.segments.join by 
    have h' := cs₁.wfExec.choose_spec.equiv_changes_eq_result cs₂.wfExec.choose_spec h
    have h₁ : cs₁.endState.rtr = s₁.rtr := by simp [cs₁.wfEndState]
    have h₂ : cs₂.endState.rtr = s₂.rtr := by simp [cs₂.wfEndState]
    simp [←h₁, ←h₂, h']
  sorry -- TODO: This is the next big theorem.
    
    
      