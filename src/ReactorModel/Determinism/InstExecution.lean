import ReactorModel.Determinism.InstStep

open Classical

namespace Execution

theorem InstExecution.preserves_tag : (s₁ ⇓ᵢ+ s₂) → s₁.ctx.tag = s₂.ctx.tag
  | single h => h.exec.preserves_tag
  | trans h hi => h.exec.preserves_tag.trans hi.preserves_tag

theorem InstExecution.preserves_ctx_past_future {s₁ s₂} :
  (s₁ ⇓ᵢ+ s₂) → ∀ g, g ≠ s₁.ctx.tag → s₁.ctx.processedRcns g = s₂.ctx.processedRcns g := by
  intro h g hg
  induction h
  case single h => exact h.exec.preserves_ctx_past_future _ hg
  case trans s₁ _ sₘ he _ hi =>
    rw [InstExecution.preserves_tag $ single he] at hg
    exact (he.exec.preserves_ctx_past_future _ hg).trans $ hi hg
    
theorem InstExecution.preserves_rcns {i : ID} :
  (s₁ ⇓ᵢ+ s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i)
  | single h => h.exec.preserves_rcns
  | trans h₁ₘ hₘ₂ => h₁ₘ.exec.preserves_rcns.trans hₘ₂.preserves_rcns

theorem InstExecution.rcns_unprocessed : 
  (e : s₁ ⇓ᵢ+ s₂) → ∀ rcn ∈ e.rcns, rcn ∉ s₁.ctx.currentProcessedRcns := by
  intro h rcn hr
  induction h
  case single h => 
    simp [rcns] at hr
    have h := h.rcn_unprocessed
    simp [InstStep.rcn] at h
    simp [hr, h]
  case trans hi =>
    cases List.mem_cons.mp hr
    case inl h _ hc => 
      simp [rcns] at hc
      have h := h.rcn_unprocessed
      simp [InstStep.rcn, ←hc] at h
      exact h
    case inr h₁ _ h => 
      specialize hi h
      exact ((not_or _ _).mp $ (mt h₁.mem_currentProcessedRcns.mpr) hi).right

theorem InstExecution.rcns_nodup : (e : s₁ ⇓ᵢ+ s₂) → List.Nodup e.rcns
  | single _ => List.nodup_singleton _
  | trans h₁ h₂ => List.nodup_cons.mpr $ ⟨(mt $ h₂.rcns_unprocessed _) $ not_not.mpr h₁.self_currentProcessedRcns, h₂.rcns_nodup⟩

theorem InstExecution.ops_nodup : (e : s₁ ⇓ᵢ+ s₂) → List.Nodup e.ops := by
  intro e
  induction e
  case single => apply List.nodup_singleton
  case trans hd tl h =>
    simp [ops, List.nodup_cons, h]
    by_contra hm
    have h' := tl.rcns_unprocessed hd.op.rcn
    simp [rcns, List.mem_map] at h'
    specialize h' hd.op hm rfl
    simp [hd.exec.ctx_adds_rcn, Context.addCurrentProcessed_mem_currentProcessedRcns] at h'

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
  case single h => simp [InstStep.rcn, rcns, List.mem_singleton, h.mem_currentProcessedRcns]
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
  (e : s₁ ⇓ᵢ+ s₂) → (s₁ -[e.changes]→* ⟨s₂.rtr, s₁.ctx⟩) := by
  intro e
  induction e
  case single e => simp [changes, e.exec.to_ChangeListStep]
  case trans s₁ sₘ s₂ e₁ e₂ hi => 
    have h := e₁.exec.to_ChangeListStep
    simp [changes]
    have hs := ChangeListStep.append h hi rfl
    exact hs

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
    simp [rcns] at h
    simp [rcns, h.right] at h'

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

theorem InstExecution.mem_ops_split (e : s₁ ⇓ᵢ+ s₂) :
  (op ∈ e.ops) → 
  ∃ (sₘ₁ : _) (sₘ₂ : _) (e₁ : s₁ ⇓ᵢ* sₘ₁) (eₘ : sₘ₁ ⇓ᵢ sₘ₂) (e₂ : sₘ₂ ⇓ᵢ* s₂), 
  (e = e₁ ++ eₘ ++ e₂) ∧ (eₘ.op = op) :=
  sorry

theorem InstExecution.same_rcns_same_ops (e₁ : s ⇓ᵢ+ s₁) (e₂ : s ⇓ᵢ+ s₂) :
  (e₁.rcns ~ e₂.rcns) → (e₁.ops ~ e₂.ops) := by
  intro hp
  simp [List.perm_ext e₁.ops_nodup e₂.ops_nodup]
  intro op
  suffices H : ∀ {s₁ s₂} (e₁ : s ⇓ᵢ+ s₁) (e₂ : s ⇓ᵢ+ s₂), (e₁.rcns ~ e₂.rcns) → ∀ {op}, op ∈ e₁.ops → op ∈ e₂.ops 
    from ⟨H e₁ e₂ hp, H e₂ e₁ hp.symm⟩
  intro s₁ s₂ e₁ e₂ hp op h
  have ⟨sₘ₁, sₘ₂, hd₁, eₘ, tl₂, he, ho⟩ := e₁.mem_ops_split h
  have H0 := eₘ.wfOp
  have H1 : op.rcn ∈ e₁.rcns := by
    simp [rcns, List.mem_map]
    exact ⟨_, h, rfl⟩
  have H2 : op.rcn ∈ e₂.rcns := 
    hp.mem_iff.mp H1
  have ⟨op', H4, H3⟩ : ∃ op', op' ∈ e₂.ops ∧ op.rcn = op'.rcn := by
    simp [rcns, List.mem_map] at H2
    exact H2
  have ⟨sₘ₁', sₘ₂', hd₁', eₘ', tl₂', he', ho'⟩ :=
    e₂.mem_ops_split H4
  have H5 := eₘ'.wfOp
  suffices h : sₘ₁.operation op.rcn = sₘ₁'.operation op.rcn by
    skip
    rw [ho', ←H3, ←h, ←ho, H0, Option.some_inj, ho] at H5
    simp [H5, H4]

  sorry 
  -- NOTE: hd₁ and hd₁' don't have to contain the same process the same rcns.
  --       they can be of completely different "length".
  --       but they *do* need to contain precisely all dependencies of op.rcn and none of its antidependencies!
  --
  -- TODO: perhaps extract this into a lemma. 
  -- the key features are:
  -- * the precise op.rcn is irrelevant, we only need to know that ...?
  --    1. it is not contained in hd₁/hd₁'.rcns ? 
  -- 
  -- ... continue the list

theorem InstExecution.same_rcns_ChangeListEquiv :
  (e₁ : s ⇓ᵢ+ s₁) → (e₂ : s ⇓ᵢ+ s₂) → (e₁.rcns ~ e₂.rcns) → (e₁.changes ⋈ e₂.changes) := by
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
    
    
      