import ReactorModel.Execution.Basic

open Classical Port

def List.lastSome? (l : List α) (p : α → Option β) : Option β :=
  l.reverse.findSome? p

-- This file defines (and proves) determinism for the reactor model.
-- Determinism can be understood in multiple ways.
-- Primarily, we say the execution is deterministic if there is always at most one timed
-- step that can be taken.
namespace Execution

theorem ChangeStep.mutates_comm {s s₁ s₂ s₁₂ s₂₁ : State} {rcn₁ rcn₂ : ID} {c₁ c₂ : Change} : 
  (s -[rcn₁:c₁]→ s₁) → (s₁ -[rcn₂:c₂]→ s₁₂) → 
  (s -[rcn₂:c₂]→ s₂) → (s₂ -[rcn₁:c₁]→ s₂₁) → 
  c₁.mutates → s₁₂ = s₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hm
  cases c₁ 
  <;> (simp only [Change.mutates] at hm) 
  <;> (
    cases c₂
    case' port, state, action => 
      cases h₁; cases h₂; cases h₁₂; cases h₂₁
      sorry -- exact Reactor.Update.unique' (by assumption) (by assumption)
  )
  <;> (cases h₁; cases h₂; cases h₁₂; cases h₂₁; rfl)
  
theorem ChangeStep.mutates_comm' {s s₁ s₂ s₁₂ s₂₁ : State} {rcn₁ rcn₂ : ID} {c₁ c₂ : Change} : 
  (s -[rcn₁:c₁]→ s₁) → (s₁ -[rcn₂:c₂]→ s₁₂) → 
  (s -[rcn₂:c₂]→ s₂) → (s₂ -[rcn₁:c₁]→ s₂₁) → 
  (c₁.mutates ∨ c₂.mutates) → s₁₂ = s₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hm
  cases hm
  case inl h => exact ChangeStep.mutates_comm h₁ h₁₂ h₂ h₂₁ h
  case inr h => exact (ChangeStep.mutates_comm h₂ h₂₁ h₁ h₁₂ h).symm

/-
theorem ChangeStep.ne_cmp_comm {s s₁ s₂ s₁₂ s₂₁ : State} {rcn₁ rcn₂ : ID} {c₁ c₂ : Change} : 
  (s -[rcn₁:c₁]→ s₁) → (s₁ -[rcn₂:c₂]→ s₁₂) → 
  (s -[rcn₂:c₂]→ s₂) → (s₂ -[rcn₁:c₁]→ s₂₁) → 
  (¬ c₁ ≈ c₂) → s₁₂ = s₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hc
  by_cases hm : c₁.mutates ∨ c₂.mutates
  case pos => exact ChangeStep.mutates_comm' h₁ h₁₂ h₂ h₂₁ hm
  case neg =>
    cases c₁ <;> cases c₂ <;> (simp only [not_or, Change.mutates] at *) <;> (
      cases h₁; case _ h₁ => cases h₁₂; case _ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ h₂₁ =>
      simp [Reactor.Update.ne_cmp_ne_rtr_comm h₁ h₁₂ h₂ h₂₁ (by intro; contradiction) (by intro; contradiction) (by intro; contradiction)]
    )

theorem ChangeStep.indep_comm {s s₁ s₂ s₁₂ s₂₁ : State} {rcn₁ rcn₂ : ID} {c₁ c₂ : Change} :
  (s -[rcn₁:c₁]→ s₁) → (s₁ -[rcn₂:c₂]→ s₁₂) → 
  (s -[rcn₂:c₂]→ s₂) → (s₂ -[rcn₁:c₁]→ s₂₁) → 
  (∀ i₁ i₂, c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) → 
  s₁₂ = s₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ ht
  by_cases hm : c₁.mutates ∨ c₂.mutates
  case pos => exact ChangeStep.mutates_comm' h₁ h₁₂ h₂ h₂₁ hm
  case neg => 
    simp only [not_or] at hm
    have ⟨i₁, hi₁⟩ := mt (c₁.target_none_iff_mutates.mp) hm.left  |> Option.ne_none_iff_exists.mp
    have ⟨i₂, hi₂⟩ := mt (c₂.target_none_iff_mutates.mp) hm.right |> Option.ne_none_iff_exists.mp
    have ht' := ht i₁ i₂ hi₁.symm hi₂.symm
    have ht'' : c₁.target ≠ c₂.target := by simp [←hi₁, ←hi₂, ht']
    cases c₁ <;> cases c₂ <;> simp [Change.target] at ht''
    case' port.port, state.state, action.action => 
      cases h₁; case _ h₁ => cases h₁₂; case _ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ h₂₁ =>
      sorry -- exact Reactor.Update.ne_id_ne_rtr_comm h₁ h₁₂ h₂ h₂₁ ht'' (by intro; contradiction)
    all_goals { exact ChangeStep.ne_cmp_comm h₁ h₁₂ h₂ h₂₁ (by intro; contradiction) }
-/

theorem ChangeStep.unique {s s₁ s₂ : State} {rcn : ID} {c : Change} :
  (s -[rcn:c]→ s₁) → (s -[rcn:c]→ s₂) → s₁ = s₂ := by
  intro h₁ h₂ 
  cases h₁ <;> cases h₂
  case' port.port h₁ _ h₂, state.state h₁ _ h₂, action.action h₁ _ h₂ => simp [Reactor.Update.unique' h₁ h₂]
  all_goals { rfl }

theorem ChangeStep.preserves_ctx {s₁ s₂ : State} {rcn : ID} {c : Change} :
  (s₁ -[rcn:c]→ s₂) → s₁.ctx = s₂.ctx := 
  λ h => by cases h <;> rfl

theorem ChangeStep.preserves_rcns {i : ID} :
  (s₁ -[rcn:c]→ s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i) :=
  λ h => by cases h <;> simp <;> simp [Reactor.Update.preserves_ne_cmp_or_id (by assumption)]

/-
 /- For each cmp:i, the change of value either happens in cs₁ or in cs₂.
    This is expressed in the following two lemmas, that say that one of the two
    ChangeLists is a noop for cmp:i, one for the first step and one for the second
    step.
 -/
theorem ChangeListStep.first_step_noop {s s₁ s₂ s₁₂ s₂₁ : State} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} :
  (s -[rcn₁:cs₁]→* s₁) → (s₁ -[rcn₂:cs₂]→* s₁₂) →
  (s -[rcn₂:cs₂]→* s₂) → (s₂ -[rcn₁:cs₁]→* s₂₁) →
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  ∀ cmp i v, (s.rtr *[cmp:i]= v) → (s₁.rtr *[cmp:i]= v ∨ s₂.rtr *[cmp:i]= v) := by
  intro h₁ h₁₂ h₂ h₂₁ hi cmp i v hv
  sorry -- s₁₂ and s₂₁ are completely irrelevant



theorem ChangeListStep.first_step_op {s s₁ s₂ s₁₂ s₂₁ : State} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} :
  (s -[rcn₁:cs₁]→* s₁) → (s₁ -[rcn₂:cs₂]→* s₁₂) →
  (s -[rcn₂:cs₂]→* s₂) → (s₂ -[rcn₁:cs₁]→* s₂₁) →
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  ∀ cmp i v, (s₁₂.rtr *[cmp:i]= v) → (s₁.rtr *[cmp:i]= v ∨ s₂.rtr *[cmp:i]= v) := by
  sorry  

theorem ChangeListStep.value_identical {s s₁ s₂ s₁₂ s₂₁ : State} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} :
  (s -[rcn₁:cs₁]→* s₁) → (s₁ -[rcn₂:cs₂]→* s₁₂) →
  (s -[rcn₂:cs₂]→* s₂) → (s₂ -[rcn₁:cs₁]→* s₂₁) →
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  ∀ cmp i v, s₁₂.rtr *[cmp:i]= v → s₂₁.rtr *[cmp:i]= v := by
  intros h₁ h₁₂ h₂ h₂₁ hi cmp i v hv₁₂
  cases first_step_op h₁ h₁₂ h₂ h₂₁ hi cmp i v hv₁₂
  case inl hv₁ =>
    cases hv₁
    case root hr => sorry
    case nest s hs => sorry
  case inr hv₂ =>
    sorry
-/

/-
 -- This will be much more interesting once mutations are in the game!
theorem ChangeListStep.indep_comm_ids {s s₁ s₂ s₁₂ s₂₁ : State} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} :
  (s -[rcn₁:cs₁]→* s₁) → (s₁ -[rcn₂:cs₂]→* s₁₂) →
  (s -[rcn₂:cs₂]→* s₂) → (s₂ -[rcn₁:cs₁]→* s₂₁) →
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  s₁₂.rtr.allIDs = s₂₁.rtr.allIDs := by
  intros hσσ₁ hσ₁σ₁₂ hσσ₂ hσ₂σ₂₁ his
  sorry
-/

theorem ChangeListStep.preserves_ctx {s₁ s₂ : State} {rcn : ID} {cs : List Change} : 
  (s₁ -[rcn:cs]→* s₂) → s₁.ctx = s₂.ctx := by
  intro h
  induction h with
  | nil => rfl
  | cons h₁₂ _ h₂₃ => exact h₁₂.preserves_ctx.trans h₂₃

theorem ChangeListStep.preserves_rcns {i : ID} : 
  (s₁ -[rcn:cs]→* s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i) := by
  intro h
  induction h with
  | nil => rfl
  | cons h₁₂ _ h₂₃ => exact h₁₂.preserves_rcns.trans h₂₃

/-
theorem ChangeListStep.indep_comm {s s₁ s₂ s₁₂ s₂₁ : State} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} : 
  (s -[rcn₁:cs₁]→* s₁) → (s₁ -[rcn₂:cs₂]→* s₁₂) → 
  (s -[rcn₂:cs₂]→* s₂) → (s₂ -[rcn₁:cs₁]→* s₂₁) → 
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  s₁₂ = s₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ ht
  have hIDs := ChangeListStep.indep_comm_ids h₁ h₁₂ h₂ h₂₁ ht
  apply State.ext
  case rtr =>
    apply Reactor.Object.ext hIDs
    intros cmp i v h₁₂v
    apply ChangeListStep.value_identical h₁ h₁₂ h₂ h₂₁ ht cmp i v h₁₂v
  case ctx =>
    sorry -- follows from ChangeListStep.preserves_ctx
-/


------------------------------------------------------------------------------------------------------




-- NOTE: This only holds without mutations.
theorem ChangeStep.rcn_agnostic : (s -[rcn₁:c]→ s₁) → (s -[rcn₂:c]→ s₂) → s₁ = s₂ := by
  intro h₁ h₂
  cases h₁ <;> cases h₂ <;> simp
  case' port.port h₁ _ h₂, state.state h₁ _ h₂, action.action h₁ _ h₂ => exact Reactor.Update.unique' h₁ h₂

-- NOTE: This only holds without mutations.
theorem ChangeListStep.rcn_agnostic : (s -[rcn₁:cs]→* s₁) → (s -[rcn₂:cs]→* s₂) → s₁ = s₂
  | nil .., nil .. => rfl
  | cons h₁ hi₁ , cons h₂ hi₂ => by rw [h₁.rcn_agnostic h₂] at hi₁; exact hi₁.rcn_agnostic hi₂

-- IDEA:
-- Is it simpler to express this notion somehow by first defining a function that collapses
-- "absorbed" changes and then require the resulting lists be permutations of eachother
-- (this won't work for actions, but will for ports and states)?
-- We could then also prove a "small" lemma first, that states that the collapsed list produces
-- the same ChangeList result as the non-collapsed one.
-- Then we can use that lemma to show that ChangeListEquiv lists produce equal
-- ChangeList results.
structure ChangeListEquiv (cs₁ cs₂ : List Change) : Prop where
  ports   : ∀ i,   cs₁.lastSome? (·.portValue? i)     = cs₂.lastSome? (·.portValue? i)
  state   : ∀ i,   cs₁.lastSome? (·.stateValue? i)    = cs₂.lastSome? (·.stateValue? i)
  actions : ∀ i t, cs₁.filterMap (·.actionValue? i t) = cs₂.filterMap (·.actionValue? i t)
  -- NOTE: Mutations are currently noops, and can therefore be ignored.

notation cs₁:max " ⋈ " cs₂:max => ChangeListEquiv cs₁ cs₂

theorem ChangeListStep.equiv_changes_eq_result {cs₁ cs₂ : List Change} :
  (s -[rcn₁:cs₁]→* s₁) → (s -[rcn₂:cs₂]→* s₂) → (cs₁ ⋈ cs₂) → s₁ = s₂ := by
  intro h₁ h₂ he
  -- *[] extensionality should work here.
  sorry




------------------------------------------------------------------------------------------------------




theorem ChangeStep.preserves_unchanged_port {i : ID} :
  (s₁ -[rcn:c]→ s₂) → (∀ v, .port i v ≠ c) → (s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i) := by
  intro h hc 
  cases h <;> simp
  case port i' v h =>
    refine Reactor.Update.preserves_ne_cmp_or_id h (.inr ?_) (by simp) (by simp)
    by_contra hi
    specialize hc v
    rw [hi] at hc
    contradiction
  case' state h, action h => exact Reactor.Update.preserves_ne_cmp_or_id h (.inl $ by simp) (by simp) (by simp)

theorem ChangeStep.preserves_unchanged_action {i : ID} :
  (s₁ -[rcn:c]→ s₂) → (∀ t v, .action i t v ≠ c) → (s₁.rtr.obj? .act i = s₂.rtr.obj? .act i) := by
  intro h hc 
  cases h <;> simp
  case action i' t v h =>
    refine Reactor.Update.preserves_ne_cmp_or_id h (.inr ?_) (by simp) (by simp)
    by_contra hi
    specialize hc t v
    rw [hi] at hc
    contradiction
  case' state h, port h => exact Reactor.Update.preserves_ne_cmp_or_id h (.inl $ by simp) (by simp) (by simp)

theorem ChangeListStep.preserves_unchanged_ports {i : ID} :
  (s₁ -[rcn:cs]→* s₂) → (∀ v, .port i v ∉ cs) → (s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i) := by
  intro h hc 
  induction h
  case nil => rfl
  case cons h _ hi => 
    refine (h.preserves_unchanged_port ?_).trans (hi ?_) <;> (
      intro v
      have ⟨_, _⟩ := (not_or ..).mp $ (mt List.mem_cons.mpr) $ hc v
      assumption
    )

theorem ChangeListStep.preserves_unchanged_actions {i : ID} :
  (s₁ -[rcn:cs]→* s₂) → (∀ t v, .action i t v ∉ cs) → (s₁.rtr.obj? .act i = s₂.rtr.obj? .act i) := by
  intro h hc 
  induction h
  case nil => rfl
  case cons h _ hi => 
    refine (h.preserves_unchanged_action ?_).trans (hi ?_) <;> (
      intro t v
      have ⟨_, _⟩ := (not_or ..).mp $ (mt List.mem_cons.mpr) $ hc t v
      assumption
    )

theorem InstStep.rtr_contains_rcn : (s₁ ⇓ᵢ[rcn] s₂) → s₁.rtr.contains .rcn rcn
  | skipReaction h _ _ => h
  | execReaction _ _ h _ => State.rcnOutput_to_contains h
  
theorem InstStep.preserves_freshID : (s₁ ⇓ᵢ[rcn] s₂) → s₁.ctx.freshID = s₂.ctx.freshID
  | execReaction _ _ _ h => by simp [h.preserves_ctx]
  | skipReaction .. => rfl
  
theorem InstStep.preserves_rcns {i : ID} : 
  (s₁ ⇓ᵢ[rcn] s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i) 
  | execReaction _ _ _ h => by simp [h.preserves_rcns]
  | skipReaction .. => rfl

theorem InstStep.preserves_ctx_past_future :
  (s₁ ⇓ᵢ[rcn] s₂) → ∀ g, g ≠ s₁.ctx.time → s₁.ctx.processedRcns g = s₂.ctx.processedRcns g :=
  λ h g hg => match h with
  | execReaction _ _ _ h => by simp [←h.preserves_ctx, s₁.ctx.addCurrentProcessed_preserves_ctx_past_future _ _ hg]
  | skipReaction .. => by simp [s₁.ctx.addCurrentProcessed_preserves_ctx_past_future _ _ hg]

theorem InstStep.preserves_time : (s₁ ⇓ᵢ[rcns] s₂) → s₁.ctx.time = s₂.ctx.time := by
  intro h
  cases h <;> simp [Context.addCurrentProcessed_same_time]
  case execReaction h => simp [h.preserves_ctx]

theorem InstStep.ctx_adds_rcn : (s₁ ⇓ᵢ[rcn] s₂) → s₂.ctx = s₁.ctx.addCurrentProcessed rcn
  | execReaction _ _ _ h => by simp [h.preserves_ctx]
  | skipReaction .. => rfl

theorem InstStep.rcn_unprocessed : (s₁ ⇓ᵢ[rcn] s₂) → rcn ∉ s₁.ctx.currentProcessedRcns
  | execReaction h _ _ _ | skipReaction _ h _ => h.unprocessed
  
theorem InstStep.mem_currentProcessedRcns :
  (s₁ ⇓ᵢ[rcn] s₂) → (rcn' ∈ s₂.ctx.currentProcessedRcns ↔ rcn' = rcn ∨ rcn' ∈ s₁.ctx.currentProcessedRcns) := by
  intro h
  constructor
  case mp =>
    intro ho
    by_cases hc : rcn' = rcn
    case pos => exact .inl hc
    case neg =>
      rw [h.ctx_adds_rcn] at ho
      simp [Context.addCurrentProcessed_mem_currentProcessedRcns.mp ho]
  case mpr =>
    intro ho
    by_cases hc : rcn' = rcn
    case pos =>
      simp [hc]
      cases h <;> exact Context.addCurrentProcessed_mem_currentProcessedRcns.mpr (.inl rfl)
    case neg =>
      simp [h.ctx_adds_rcn, Context.addCurrentProcessed_mem_currentProcessedRcns.mpr (.inr $ ho.resolve_left hc)]

-- Corollary of `InstStep.mem_currentProcessedRcns`.
theorem InstStep.not_mem_currentProcessedRcns :
  (s₁ ⇓ᵢ[rcn] s₂) → (rcn' ≠ rcn) → rcn' ∉ s₁.ctx.currentProcessedRcns → rcn' ∉ s₂.ctx.currentProcessedRcns := 
  λ h hn hm => (mt h.mem_currentProcessedRcns.mp) $ (not_or _ _).mpr ⟨hn, hm⟩

-- Corollary of `InstStep.mem_currentProcessedRcns`.
theorem InstStep.monotonic_currentProcessedRcns :
  (s₁ ⇓ᵢ[rcn] s₂) → rcn' ∈ s₁.ctx.currentProcessedRcns → rcn' ∈ s₂.ctx.currentProcessedRcns := 
  (·.mem_currentProcessedRcns.mpr $ .inr ·)

-- Corollary of `InstStep.mem_currentProcessedRcns`.
theorem InstStep.self_currentProcessedRcns : 
  (s₁ ⇓ᵢ[rcn] s₂) → rcn ∈ s₂.ctx.currentProcessedRcns := 
  (·.mem_currentProcessedRcns.mpr $ .inl rfl)

-- If a port is not in the output-dependencies of a given reaction,
-- then any instantaneous step of the reaction will keep that port
-- unchanged.
theorem InstStep.preserves_nondep_ports : 
  (s₁ ⇓ᵢ[i] s₂) → (s₁.rtr.obj? .rcn i = some rcn) → 
  (p ∉ rcn.deps .out) → (s₁.rtr.obj? .prt p = s₂.rtr.obj? .prt p) := by
  intro h hr hd
  cases h 
  case skipReaction => rfl
  case execReaction hr' _ ho hs => exact hs.preserves_unchanged_ports (s₁.rcnOutput_port_dep_only · ho hr hd)

theorem InstStep.preserves_nondep_actions : 
  (s₁ ⇓ᵢ[i] s₂) → (s₁.rtr.obj? .rcn i = some rcn) → 
  (a ∉ rcn.deps .out) → (s₁.rtr.obj? .act a = s₂.rtr.obj? .act a) := by
  intro h hr hd
  cases h 
  case skipReaction => rfl
  case execReaction hr' _ ho hs => exact hs.preserves_unchanged_actions (s₁.rcnOutput_action_dep_only · · ho hr hd)

theorem InstStep.pure_preserves_state : 
  (s₁ ⇓ᵢ[i] s₂) → (s₁.rtr.obj? .rcn i = some rcn) → (rcn.isPure) → 
  (s₁.rtr.con? .rcn i = some c₁) → (s₂.rtr.con? .rcn i = some c₂) →
  (c₁.obj.state = c₂.obj.state) := by
  intro h hr hp hc₁ hc₂
  cases h 
  case skipReaction => rfl
  case execReaction hr' _ ho hs => 
    sorry

theorem InstStep.acyclic_deps : (s₁ ⇓ᵢ[rcn] s₂) → (rcn >[s₁.rtr]< rcn) :=
  λ h => by cases h <;> exact State.allows_requires_acyclic_deps $ by assumption

theorem InstStep.indep_rcns_indep_output :
  (s ⇓ᵢ[rcn'] s') → (rcn >[s.rtr]< rcn') → s.rcnOutput rcn = s'.rcnOutput rcn := by
  intro h hi
  have hp := h.preserves_rcns (i := rcn)
  cases ho : s.rtr.obj? .rcn rcn <;> cases ho' : s'.rtr.obj? .rcn rcn 
  case none.none => simp [State.rcnOutput, ho, ho']
  case' none.some, some.none => simp [hp, ho'] at ho
  case some.some => 
    have ⟨⟨p, a, x, t⟩, hj⟩ := State.rcnInput_iff_obj?.mpr ⟨_, ho⟩
    have ⟨⟨p', a', x', t'⟩, hj'⟩ := State.rcnInput_iff_obj?.mpr ⟨_, ho'⟩
    have H1 : p = p' := by 
      simp [s.rcnInput_portVals_def hj ho, s'.rcnInput_portVals_def hj' ho']
      rw [←hp] at ho'
      have he := Option.some_inj.mp $ ho.symm.trans ho'
      simp [he]
      refine congr_arg2 _ ?_ rfl
      apply Finmap.restrict_ext
      intro p hp
      have ⟨_, hr⟩ := Reactor.contains_iff_obj?.mp h.rtr_contains_rcn
      have hd := hi.symm.nonoverlapping_deps hr ho'
      simp [Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter] at hd
      have hd := mt (hd p) $ not_not.mpr hp
      simp [Reactor.obj?'_eq_obj?, h.preserves_nondep_ports hr hd]
    have H2 : a = a' := by
      simp [s.rcnInput_actions_def hj ho, s'.rcnInput_actions_def hj' ho']
      rw [←hp] at ho'
      have he := Option.some_inj.mp $ ho.symm.trans ho'
      simp [he]
      apply Finmap.restrict_ext
      intro a ha
      apply Finmap.filterMap_congr
      have ⟨_, hr⟩ := Reactor.contains_iff_obj?.mp h.rtr_contains_rcn
      have hd := hi.symm.nonoverlapping_deps hr ho'
      simp [Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter] at hd
      have hd := mt (hd a) $ not_not.mpr ha
      simp [Reactor.obj?'_eq_obj?, h.preserves_nondep_actions hr hd]
    have H3 : t = t' := by 
      simp [s.rcnInput_time_def hj, s'.rcnInput_time_def hj', h.preserves_time]
    simp [H1, H2, H3] at hj
    have ⟨r, hr⟩ := Reactor.contains_iff_obj?.mp h.rtr_contains_rcn
    cases hi.ne_rtr_or_pure ho hr
    case inl he => 
      have ⟨c, hc, _⟩ := Reactor.obj?_to_con?_and_cmp? ho
      have ⟨c', hc', _⟩ := Reactor.obj?_to_con?_and_cmp? ho'
      have hs := State.rcnInput_state_def hj hc
      have hs' := State.rcnInput_state_def hj' hc'
      have HH : c.obj.state = c'.obj.state := sorry -- This follows from `he` and some lemma akin to `preserves_nondep_actions`
      rw [HH] at hs
      rw [hs.trans hs'.symm] at hj
      exact State.rcnOutput_congr (hj.trans hj'.symm) hp
    case inr hc =>
      cases hc
      case inl hp' => exact State.rcnOutput_pure_congr hj hj' ho sorry /-this is ho'-/ hp'
      case inr hp' => 
        have ⟨hp₁, hp₂⟩ := hp'
        -- Follows from x = x' which follows from hp₂
        -- Create a `preserves_nondep_actions`-type of lemma for this.
        have ⟨_, hro, _⟩ := Reactor.obj?_to_con?_and_cmp? hr
        have ⟨_, hro'⟩ : ∃ c, s'.rtr.con? .rcn rcn' = some c := sorry
        have := h.pure_preserves_state hr hp' hro hro'
        -- TODO: Turn `this` into H:
        have H : s.rcnInput rcn = s'.rcnInput rcn := sorry 
        exact State.rcnOutput_congr H hp

theorem InstStep.indep_rcns_changes_comm_equiv {s : State} :
  (rcn₁ >[s.rtr]< rcn₂) → (s.rcnOutput rcn₁ = some o₁) → (s.rcnOutput rcn₂ = some o₂) → 
  (o₁ ++ o₂) ⋈ (o₂ ++ o₁) := by
  intro hi ho₁ ho₂
  constructor <;> intro i 
  case ports =>
    -- consequence of hi: 
    -- either rcn₁ and rcn₂ and don't live in the same reactor,
    -- or if they do Reactor.rcnsTotal implies that they can't share any
    -- output dependencies. By the constraints on Reaction they thus can't
    -- produces changes to the same port.
    sorry
  case state =>
    -- consequence of hi: 
    -- either rcn₁ and rcn₂ and don't live in the same reactor,
    -- or if they do Reactor.rcnsTotal implies that they must be pure,
    -- i.e. don't produce changes to state, thus making bother sides of
    -- the equality none.
    sorry
  case actions =>
    intro t
    -- consequence of hi: 
    -- either rcn₁ and rcn₂ and don't live in the same reactor,
    -- or if they do Reactor.rcnsTotal implies that they can't share any
    -- output dependencies. By the constraints on Reaction they thus can't
    -- produces changes to the same action.
    sorry

-- WARNING: I think this brings us into reaction-swap and hence
--          intermediate reactor territory again.
--          I think what we want instead is an extension of 
--          InstStep.indep_rcns_changes_comm_equiv to reaction lists.
theorem InstStep.indep_rcns_changes_equiv :
  (s ⇓ᵢ[rcn₁] s₁) → (s ⇓ᵢ[rcn₂] s₂) → (rcn₁ >[s.rtr]< rcn₂) →
  (s.rcnOutput rcn₁ = some o₁) → (s₁.rcnOutput rcn₂ = some o₁₂) → 
  (s.rcnOutput rcn₂ = some o₂) → (s₂.rcnOutput rcn₁ = some o₂₁) → 
  (o₁ ++ o₁₂) ⋈ (o₂ ++ o₂₁) := by
  intro h₁ h₂ hi ho₁ ho₁₂ ho₂ ho₂₁
  rw [h₂.indep_rcns_indep_output hi] at ho₁
  rw [ho₁.symm.trans ho₂₁ |> Option.some_inj.mp]
  rw [h₁.indep_rcns_indep_output hi.symm] at ho₂
  rw [ho₂.symm.trans ho₁₂ |> Option.some_inj.mp]
  rw [←h₁.indep_rcns_indep_output hi.symm] at ho₁₂
  rw [←h₂.indep_rcns_indep_output hi] at ho₂₁
  exact InstStep.indep_rcns_changes_comm_equiv hi ho₂₁ ho₁₂

theorem InstExecution.preserves_freshID : (s₁ ⇓ᵢ+[rcns] s₂) → s₁.ctx.freshID = s₂.ctx.freshID
  | single h => h.preserves_freshID
  | trans h₁ₘ hₘ₂ => h₁ₘ.preserves_freshID.trans hₘ₂.preserves_freshID

theorem InstExecution.preserves_time : (s₁ ⇓ᵢ+[rcns] s₂) → s₁.ctx.time = s₂.ctx.time
  | single h => h.preserves_time
  | trans h hi => h.preserves_time.trans hi.preserves_time

theorem InstExecution.preserves_ctx_past_future {s₁ s₂ rcns} :
  (s₁ ⇓ᵢ+[rcns] s₂) → ∀ g, g ≠ s₁.ctx.time → s₁.ctx.processedRcns g = s₂.ctx.processedRcns g := by
  intro h g hg
  induction h
  case single h => exact h.preserves_ctx_past_future _ hg
  case trans s₁ s₂ sₘ he _ hi =>
    rw [InstExecution.preserves_time $ single he] at hg
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
protected theorem InstExecution.deterministic {s s₁ s₂ rcns₁ rcns₂} : 
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
  sorry

theorem State.instComplete_to_inst_stuck : s.instComplete → ∀ s' rcn, ¬(s ⇓ᵢ[rcn] s') := by
  intro h s' _ he 
  have h' := Reactor.ids_mem_iff_contains.mpr he.rtr_contains_rcn
  rw [←h] at h'
  exact absurd h' he.rcn_unprocessed

theorem CompleteInstExecution.preserves_freshID : (s₁ ⇓ᵢ| s₂) → s₁.ctx.freshID = s₂.ctx.freshID
  | mk _ e _ => e.preserves_freshID

theorem CompleteInstExecution.convergent_rcns :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.rtr.ids .rcn = s₂.rtr.ids .rcn
  | mk _ e₁ _, mk _ e₂ _ => by simp [Finset.ext_iff, Reactor.ids_mem_iff_contains, Reactor.contains_iff_obj?, ←e₁.preserves_rcns, e₂.preserves_rcns]

theorem CompleteInstExecution.convergent_ctx : 
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.ctx = s₂.ctx := by
  intro hc₁ hc₂
  apply Context.ext_iff.mpr
  refine ⟨?_, hc₁.preserves_freshID.symm.trans hc₂.preserves_freshID⟩
  apply Finmap.ext
  intro g
  have hc₁₂ := hc₁.convergent_rcns hc₂
  cases hc₁ with | mk _ e₁ hc₁ => 
  cases hc₂ with | mk _ e₂ hc₂ => 
  by_cases hg : g = s.ctx.time
  case pos => 
    have h₁ := hc₁ |> Option.some_inj.mpr
    have h₂ := hc₂ |> Option.some_inj.mpr
    rw [Context.currentProcessedRcns_def] at h₁ h₂
    simp only [←e₁.preserves_time, ←e₂.preserves_time, ←hg] at h₁ h₂
    simp only [h₁, h₂, hc₁₂]
  case neg => simp only [←e₁.preserves_ctx_past_future g hg, e₂.preserves_ctx_past_future g hg]

theorem CompleteInstExecution.convergent : (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁ = s₂ :=
  λ hc₁ hc₂ => 
    match hc₁, hc₂ with 
    | mk _ e₁ _, mk _ e₂ _ => e₁.deterministic e₂ $ hc₁.convergent_ctx hc₂

end Execution

theorem Execution.Step.time_monotone : (s₁ ⇓ s₂) → s₁.ctx.time ≤ s₂.ctx.time
  | completeInst _ (.mk _ e _) => le_of_eq e.preserves_time
  | advanceTime hg _ _ => le_of_lt $ s₁.ctx.advanceTime_strictly_increasing _ (s₁.time_lt_nextTag hg)

protected theorem Execution.Step.deterministic {s s₁ s₂ : State} : 
  (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂ := by
  intro he₁ he₂
  cases he₁ <;> cases he₂
  case completeInst.completeInst hc₁ hc₂ => 
    exact CompleteInstExecution.convergent hc₁ hc₂
  case advanceTime.advanceTime g₁ hg₁ _ h₁ _ g₂ hg₂ _ h₂ => 
    simp only [hg₁, Option.some_inj] at hg₂
    simp [clearingPorts_unique h₁ h₂, Context.advanceTime, hg₂]  
  case' completeInst.advanceTime hc _ _ _ hic _, advanceTime.completeInst _ _ _ hic _ hc => 
    cases hc with | mk _ e _ => 
    cases e; case' single hi, trans hi _ => exact False.elim $ impossible_case_aux hi hic
where
  impossible_case_aux {s₁ s₂ rcn} (hi : s₁ ⇓ᵢ[rcn] s₂) (hic : s₁.instComplete) : False := by
    exact absurd (Reactor.ids_mem_iff_contains.mpr hi.rtr_contains_rcn) $ mt (Finset.ext_iff.mp hic _).mpr <| hi.rcn_unprocessed

theorem Execution.time_monotone : (s₁ ⇓* s₂) → s₁.ctx.time ≤ s₂.ctx.time := by
  intro h
  induction h with
  | refl => simp
  | step h _ hi => exact le_trans h.time_monotone hi

protected theorem Execution.deterministic {s s₁ s₂ : State} (hc₁ : s₁.instComplete) (hc₂ : s₂.instComplete) : 
  (s ⇓* s₁) → (s ⇓* s₂) → (s₁.ctx.time = s₂.ctx.time) → s₁ = s₂ := by
  intro he₁ he₂ ht
  induction he₁ <;> cases he₂ 
  case refl.refl => rfl
  case step.refl _ _ h₂₃ _ h₁₂ => exact False.elim $ impossible_case_aux hc₂ ht.symm h₁₂ h₂₃
  case refl.step _ _ h₁₂ h₂₃ => exact False.elim $ impossible_case_aux hc₁ ht h₁₂ h₂₃
  case step.step s sₘ₁ s₁ h₁ₘ₁ hₘ₁₂ hi sₘ₂ h₁ₘ₂ hₘ₂₂ => 
    rw [Execution.Step.deterministic h₁ₘ₁ h₁ₘ₂] at hi
    exact hi hc₁ hₘ₂₂ ht
where 
  impossible_case_aux {s₁ s₂ s₃ : State} (hc : s₁.instComplete) (ht : s₁.ctx.time = s₃.ctx.time) :
    (s₁ ⇓ s₂) → (s₂ ⇓* s₃) → False := by
    intro h₁₂ h₂₃
    cases h₁₂
    case completeInst hi =>
      cases hi with | mk _ e _ =>
      cases e 
      case' single h, trans h _ => exact absurd h $ State.instComplete_to_inst_stuck hc _ _
    case advanceTime g hg _ _ => 
      have h := time_monotone h₂₃
      rw [←ht] at h
      simp only at h
      have h' := s₁.ctx.advanceTime_strictly_increasing g (s₁.time_lt_nextTag hg)
      exact (lt_irrefl _ $ lt_of_le_of_lt h h').elim
