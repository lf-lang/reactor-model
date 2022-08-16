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

theorem InstExecution.changes_nodup : (e : s₁ ⇓ᵢ+ s₂) → List.Nodup e.changes :=
  sorry -- This should hold as each change (block) is Identified.

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

-- TODO: Delete this if unused.
theorem InstExecution.rcns_respect_dependencies : 
  (e : s₁ ⇓ᵢ+ s₂) →
  e.rcns.get? i₁ = some rcn₁ → e.rcns.get? i₂ = some rcn₂ → 
  rcn₁ >[s₁.rtr] rcn₂ → i₁ < i₂ := by
  intro h h₁ h₂ hd
  sorry

theorem InstExecution.rcn_list_cons : (e : s₁ ⇓ᵢ+ s₂) → ∃ hd tl, e.rcns = hd :: tl :=
  (by cases · <;> simp [rcns])

theorem InstExecution.to_ChangeListStep :
  (e : s₁ ⇓ᵢ+ s₂) → (s₁ -[e.changes']→* ⟨s₂.rtr, s₁.ctx⟩) := by
  intro e
  induction e
  case single e => simp [changes', e.to_ChangeListStep]
  case trans s₁ sₘ s₂ e₁ e₂ hi => 
    have h := e₁.to_ChangeListStep
    simp [changes]
    have hs := ChangeListStep.append h hi rfl
    exact hs

theorem InstExecution.mem_rcns_obj? :
  {e : s₁ ⇓ᵢ+ s₂} → (rcn ∈ e.rcns) → (∃ o, s₁.rtr.obj? .rcn rcn = some o) := by
  sorry

theorem InstExecution.indep_rcns_indep_output :
  (e : s ⇓ᵢ+ s') → (∀ rcn ∈ e.rcns, rcn' >[s.rtr]< rcn ∧ rcn' ≠ rcn) → s.rcnOutput rcn' = s'.rcnOutput rcn' := by
  intro e h
  induction e
  case single h' =>
    specialize h h'.rcn (by simp [rcns])
    exact h'.indep_rcns_indep_output h.left h.right
  case trans s₁ sₘ s₂ h₁ h₂ hi =>
    specialize h h₁.rcn (by simp [rcns])
    rw [h₁.indep_rcns_indep_output h.left h.right]
    suffices h : ∀ (rcn : ID), rcn ∈ rcns h₂ → rcn' >[sₘ.rtr]< rcn ∧ rcn' ≠ rcn from hi h
    intro rcn hr
    -- TODO: Is this even provable?
    cases ho : sₘ.rtr.obj? .rcn rcn'
    case none =>
      have := h₂.mem_rcns_obj? hr
      sorry
    case some =>
      sorry

/-
theorem InstExecution.rcns_length_gt_zero : (e : s₁ ⇓ᵢ+ s₂) → e.rcns.length > 0
  | single .. => by simp [rcns]
  | trans _ h => by simp [rcns, Nat.succ_pos]
    
theorem InstExecution.nthState_zero : (e : s₁ ⇓ᵢ+ s₂) → e.nthState 0 = s₁ := by
  simp [nthState]

theorem InstExecution.nthState_rcn : 
  (e : s₁ ⇓ᵢ+ s₂) → (e.nthState i = some s) → (i > 0) → 
  ∃ (s' : _) (_ : s₁ ⇓ᵢ+ s) (e' : s ⇓ᵢ s') (_ : s' ⇓ᵢ+ s₂), e'.rcn = e.rcns[i]? := by
  sorry

theorem InstExecution.segments : 
  (e : s₁ ⇓ᵢ+ s₂) → 
  ∃ l : List (List (Identified Change)), 
    (l.join = e.changes) ∧ 
    (∀ i, e.nthState i = some s → e.rcns[i]? = some rcn → l[i]? = s.rcnOutput' rcn) 
  := by
    intro e
    induction e
    case single e =>
      exists [e.changes]
      simp [changes]
      intro i hi hr
      cases i <;> simp [nthState] at hi
      subst hi
      simp [rcns] at hr
      simp [InstStep.changes]
-/      

theorem InstStep.eq_rcn_eq_changes {e₁ : s ⇓ᵢ s₁} {e₂ : s ⇓ᵢ s₂} :
  (e₁.rcn = e₂.rcn) → (e₁.changes = e₂.changes) := by
  intro h
  cases e₁ <;> cases e₂ <;> (simp [rcn] at h; simp [changes])
  case skipReaction.skipReaction => 
    exact h
  case execReaction.execReaction h₁ _ _ _ _ _ _ h₂ _ =>
    simp [h] at h₁
    simp [Option.some_inj.mp <| h₁.symm.trans h₂]
  case' execReaction.skipReaction h', skipReaction.execReaction h' _ _ =>
    simp [←h] at h'
    contradiction 

theorem InstExecution.rcns_singleton (e : s₁ ⇓ᵢ+ s₂) :
  (e.rcns = [rcn]) → ∃ e' : s₁ ⇓ᵢ s₂, (e'.rcn = rcn) ∧ (e = single e') := by
  intro h
  cases e
  case single e =>
    exists e
    simp [rcns] at h
    exact ⟨h, rfl⟩
  case trans hd tl => 
    have ⟨_, _, h'⟩ := tl.rcn_list_cons
    simp [rcns, h'] at h

-- Reflexive closure for InstExecution
inductive InstExecution.RC : State → State → Type
  | rfl (s) : RC s s 
  | exec : s₁ ⇓ᵢ+ s₂ → RC s₁ s₂

notation s₁:max " ⇓ᵢ* " s₂:max => InstExecution.RC s₁ s₂

def InstExecution.RC.appendStep : (s₁ ⇓ᵢ* s₂) → (s₂ ⇓ᵢ s₃) → (s₁ ⇓ᵢ+ s₃)
  | rfl .., e => single e
  | exec e₁, e₂ => e₁ ++ e₂

instance : HAppend (s₁ ⇓ᵢ* s₂) (s₂ ⇓ᵢ s₃) (s₁ ⇓ᵢ+ s₃) where
  hAppend e₁ e₂ := e₁.appendStep e₂

def InstExecution.appendRC (e₁ : s₁ ⇓ᵢ+ s₂) : (s₂ ⇓ᵢ* s₃) → (s₁ ⇓ᵢ+ s₃) 
  | .rfl .. => e₁
  | .exec e₂ => e₁ ++ e₂

instance : HAppend (s₁ ⇓ᵢ+ s₂) (s₂ ⇓ᵢ* s₃) (s₁ ⇓ᵢ+ s₃) where
  hAppend e₁ e₂ := e₁.appendRC e₂

theorem InstExecution.mem_changes_split (e : s₁ ⇓ᵢ+ s₂) :
  (cs ∈ e.changes) → 
  ∃ (sₘ₁ : _) (sₘ₂ : _) (e₁ : s₁ ⇓ᵢ* sₘ₁) (eₘ : sₘ₁ ⇓ᵢ sₘ₂) (e₂ : sₘ₂ ⇓ᵢ* s₂), 
  (e = e₁ ++ eₘ ++ e₂) ∧ (eₘ.changes = cs) :=
  sorry

theorem InstExecution.same_rcns_same_change_segments (e₁ : s ⇓ᵢ+ s₁) (e₂ : s ⇓ᵢ+ s₂) :
  (e₁.rcns ~ e₂.rcns) → (e₁.changes ~ e₂.changes) := by
  intro hp
  /-induction e₁ 
  case single e₁ =>
    simp [rcns] at hp
    have hp := List.perm.eq_singleton hp.symm
    have ⟨_, h₁, h₂⟩ := e₂.rcns_singleton hp
    simp [h₂, changes, InstStep.eq_rcn_eq_changes h₁, List.Perm.refl]
  -/
  simp [List.perm_ext e₁.changes_nodup e₂.changes_nodup]
  intro cs
  constructor <;> intro h
  case mp =>
    have h' := e₁.mem_changes_split h
    sorry
  -- if a change appears in e₁, that means that it must have been produced by some unique rcn ∈ e₁.rcns.
  -- since e₂.rcns must also contain this rcn, we only need to show that it must produce the same change.
  --
  -- same holds in the other direction.
    

theorem InstExecution.same_rcns_ChangeListEquiv :
  (e₁ : s ⇓ᵢ+ s₁) → (e₂ : s ⇓ᵢ+ s₂) → (e₁.rcns ~ e₂.rcns) → (e₁.changes' ⋈ e₂.changes') := by
  intro e₁ e₂ hp
  sorry
  -- prove that the changes produced by each reaction are the same (somehow using InstStep.indep_rcns_indep_output)?
  --
  -- * say that there exists a l₁ : List (List Change) such that l.join = e₁.changes
  --   and for each index i in 0 to rcns.length: e₁[0...i].rcnOutput e₁.rcns[i] = l₁[i]
  -- * same holds for an l₂ with e₂
  -- * the prove that for each rcn ∈ e₁.rcns/e₂.rcns the entries in l₁/l₂ correspond
  -- 
  -- * lastly show that this must imply change list equivalence?
  --
  -- extensionality?
  --
  -- can we perform an induction over the length of the list?
  -- for length 0 it's trivial
  -- for length n + 1:
  --   we know the head element must have no dependencies on any other elements in the list otherwise
  --   (by e₁ and e₂) it could not be the head
  -- 
  -- 
  -- Proof steps:
  -- 1. Formalize the condition of a reaction list being dependency-preserving (aka topologically sorted).

  

-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
protected theorem InstExecution.deterministic : 
  (s ⇓ᵢ+ s₁) → (s ⇓ᵢ+ s₂) → (s₁.ctx = s₂.ctx) → s₁ = s₂ := by
  intro h₁ h₂ hc
  refine State.ext _ _ ?_ hc
  have hp := h₁.eq_ctx_processed_rcns_perm h₂ hc
  have he := h₁.same_rcns_ChangeListEquiv h₂ hp
  injection h₁.to_ChangeListStep.equiv_changes_eq_result h₂.to_ChangeListStep he
  assumption
    
    
      