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
  case trans s₁ s₂ sₘ he _ hi =>
    rw [InstExecution.preserves_tag $ single he] at hg
    exact (he.preserves_ctx_past_future _ hg).trans $ hi hg
    
-- NOTE: This won't hold once we introduce mutations.
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
  | single h => List.nodup_singleton _
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

-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
protected theorem InstExecution.deterministic : 
  (s ⇓ᵢ+[rcns₁] s₁) → (s ⇓ᵢ+[rcns₂] s₂) → (s₁.ctx = s₂.ctx) → s₁ = s₂ := by
  intro h₁ h₂ hc
  refine State.ext _ _ ?_ hc
  have hp := h₁.eq_ctx_processed_rcns_perm h₂ hc

  -- PLAN:
  --
  -- ✔︎ `ChangeListEquiv`
  -- | two change lists are equivalent if they produce the same effects
  -- | e.g. [.prt A 3, .prt A 5] ⋈ [.prt A 5]
  -- | importantly: you have to define this not in terms of the execution relations,
  -- | but rather by the order of changes in the lists (otherwise the following theorem
  -- | would hold by definition) - that is, the relation itself should be structural,
  -- | the following lemma then ties that into behaviour:
  --
  -- 1. equivalent change lists produce equal reactors
  -- (s -[cs₁]→ s₁) → (s -[cs₂]→ s₂) → cs₁ ~ cs₂ → s₁ = s₂
  -- ... to prove this we will need to solve the theorems relating to `Change(List)Step`.
  --
  -- WIP: `InstStep.indep_rcns_changes_equiv`
  -- 2. swapping independent reactions produces equivalent change lists:
  -- (s ⇓ᵢ[r₁] s₁) → (s ⇓ᵢ[r₂] s₂) → /r₁ indep r₂/ → /r₁ and r₂ correspond to rcn₁ and rcn₂/ →
  -- (rcn₁ $ s.rcnInput rcn₁) ++ (rcn₂ $ s₁.rcnInput rcn₂) ⋈ (rcn₂ $ s.rcnInput rcn₂) ++ (rcn₁ $ s₂.rcnInput rcn₁)
  --
  -- 3. dependency respecting reaction lists that are permutations of eachother are
  -- equal up to swapping of independent reactions
  --
  -- 4. by 2. and 3. and induction: dependency respecting reaction lists that are permutations
  -- of eachother produce equivalent change lists
  -- .. how do you even state this though? 
  -- Naively we would need to lift a reaction's change list into the type level of InstStep as well (called `o` there).
  --
  -- 5. by 1. and 4. and hp and `InstExecution.rcns_respect_dependencies`: 
  --    `InstExecution.deterministic` holds
  --
  -- I think this approach should solve the "intermediate reactor" problem, as we reason at the 
  -- level of change lists. Changes are "fully realized", i.e. their behaviour does not depend
  -- on the state of a reactor - thus we don't need to consider any intermediate reactors.
  -- In constrast, reasoning at the level of reactions always reaquires an associated reactor,
  -- as the behaviour of a reaction depends on its parent reactor.

  -- Theorem: In the permuted reaction list, each reaction still produces the exact same output as before.
  -- Implies: Change lists are permutations.
  --      r1       ...        rn          |      π1        ...     πn    
  -- c11 ... c1m   ...   cn1 ... cnk      | p11 ... p1l    ...   pn1 ... pnj
  sorry