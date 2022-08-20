import ReactorModel.Determinism.ChangeSteps

open Classical

namespace Execution

theorem OperationStep.deterministic : (s -[op]↣ s₁) → (s -[op]↣ s₂) → (s₁ = s₂)
  | .skip .., .skip .. => rfl
  | .exec h₁, .exec h₂ => by simp [h₁.deterministic h₂]

theorem OperationStep.preserves_Equiv : (s₁ -[op]↣ s₂) → (s₁.rtr ≈ s₂.rtr)
  | .skip => .refl
  | .exec h => h.preserves_Equiv

theorem OperationStep.preserves_rcns {i : ID} : (s₁ -[op]↣ s₂) → s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i
  | .skip .. => rfl
  | .exec h => h.preserves_rcns

theorem OperationStep.preserves_ctx_past_future :
  (s₁ -[op]↣ s₂) → ∀ g, g ≠ s₁.ctx.tag → s₁.ctx.processedRcns g = s₂.ctx.processedRcns g
  | .skip .., _, hg => by simp [s₁.ctx.addCurrentProcessed_preserves_ctx_past_future _ _ hg]
  | .exec h,  _, hg => by simp [←h.preserves_ctx, s₁.ctx.addCurrentProcessed_preserves_ctx_past_future _ _ hg]

theorem OperationStep.preserves_tag : (s₁ -[op]↣ s₂) → s₁.ctx.tag = s₂.ctx.tag
  | .skip .. => by simp [Context.addCurrentProcessed_same_tag]
  | .exec h => by simp [Context.addCurrentProcessed_same_tag, h.preserves_ctx]

theorem OperationStep.ctx_adds_rcn : (e : s₁ -[op]↣ s₂) → s₂.ctx = s₁.ctx.addCurrentProcessed op.rcn
  | .exec h => by simp [Operation.rcn, h.preserves_ctx]
  | .skip .. => rfl

theorem OperationStep.to_ChangeListStep :
  (e : s₁ -[op]↣ s₂) → (s₁ -[op.changes]→* ⟨s₂.rtr, s₁.ctx⟩) := by
  intro e
  induction e <;> simp [Operation.changes, Operation.rcn]
  case skip => exact ChangeListStep.nil
  case exec h => exact h.ctx_agnostic rfl

theorem InstStep.determinisic (e₁ : s ⇓ᵢ s₁) (e₂ : s ⇓ᵢ s₂) : (e₁.rcn = e₂.rcn) → s₁ = s₂ := by
  intro h
  rw [rcn] at h
  have h := ((h ▸ e₁.wfOp) ▸ e₂.wfOp |> Option.some_inj.mp).symm ▸ e₂.exec
  exact e₁.exec.deterministic h

theorem InstStep.rtr_contains_rcn (e : s₁ ⇓ᵢ s₂) : (s₁.rtr.contains .rcn e.rcn) :=
  s₁.operation_to_contains e.wfOp 

theorem InstStep.rcn_unprocessed (e : s₁ ⇓ᵢ s₂) : e.rcn ∉ s₁.ctx.currentProcessedRcns := 
  e.allows.unprocessed
  
theorem InstStep.mem_currentProcessedRcns :
  (e : s₁ ⇓ᵢ s₂) → (rcn' ∈ s₂.ctx.currentProcessedRcns ↔ rcn' = e.rcn ∨ rcn' ∈ s₁.ctx.currentProcessedRcns) := by
  intro h
  constructor
  case mp =>
    intro ho
    by_cases hc : rcn' = h.rcn
    case pos => exact .inl hc
    case neg =>
      rw [h.exec.ctx_adds_rcn, ←rcn] at ho
      simp [Context.addCurrentProcessed_mem_currentProcessedRcns.mp ho]
  case mpr =>
    intro ho
    by_cases hc : rcn' = h.rcn
    case pos =>
      simp [hc]
      sorry
      -- exact Context.addCurrentProcessed_mem_currentProcessedRcns.mpr (.inl rfl)
    case neg =>
      simp [h.exec.ctx_adds_rcn, Context.addCurrentProcessed_mem_currentProcessedRcns.mpr (.inr $ ho.resolve_left hc)]

-- Corollary of `InstStep.mem_currentProcessedRcns`.
theorem InstStep.not_mem_currentProcessedRcns :
  (e : s₁ ⇓ᵢ s₂) → (rcn' ≠ e.rcn) → rcn' ∉ s₁.ctx.currentProcessedRcns → rcn' ∉ s₂.ctx.currentProcessedRcns := 
  λ h hn hm => (mt h.mem_currentProcessedRcns.mp) $ (not_or _ _).mpr ⟨hn, hm⟩

-- Corollary of `InstStep.mem_currentProcessedRcns`.
theorem InstStep.monotonic_currentProcessedRcns :
  (s₁ ⇓ᵢ s₂) → rcn' ∈ s₁.ctx.currentProcessedRcns → rcn' ∈ s₂.ctx.currentProcessedRcns := 
  (·.mem_currentProcessedRcns.mpr $ .inr ·)

-- Corollary of `InstStep.mem_currentProcessedRcns`.
theorem InstStep.self_currentProcessedRcns : 
  (e : s₁ ⇓ᵢ s₂) → e.rcn ∈ s₂.ctx.currentProcessedRcns := 
  (·.mem_currentProcessedRcns.mpr $ .inl rfl)

theorem identified_changes_equiv_changes {cs : List Change} {o : List (Identified Change)} : 
  (cs.map ({ id := i, obj := ·}) = o) → (o.map (·.obj) = cs) := by
  intro h
  induction cs generalizing o
  case nil => simp_all
  case cons hd tl hi =>
    cases o <;> simp [List.map_cons] at h ⊢
    case cons hd' tl' =>
      specialize hi h.right
      simp [h.left.symm, hi]
      
-- If a port is not in the output-dependencies of a given reaction,
-- then any instantaneous step of the reaction will keep that port
-- unchanged.
theorem InstStep.preserves_nondep_ports : 
  (e : s₁ ⇓ᵢ s₂) → (s₁.rtr.obj? .rcn e.rcn = some r) → (p ∉ r.deps .out) → (s₁.rtr.obj? .prt p = s₂.rtr.obj? .prt p)
  := sorry
  /-
  | skipReaction ..,         _,  _ => rfl
  | execReaction _ _ ho hs, hr, hd => 
    hs.preserves_unchanged_ports (
      s₁.rcnOutput_port_dep_only · (by
        simp [State.rcnOutput'] at ho
        have ⟨_, hcs, ho⟩ := ho
        simp [rcn, hcs, identified_changes_equiv_changes ho]
      ) hr hd
    )
  -/

theorem InstStep.preserves_nondep_actions : 
  (e : s₁ ⇓ᵢ s₂) → (s₁.rtr.obj? .rcn e.rcn = some r) → (a ∉ r.deps .out) → (s₁.rtr.obj? .act a = s₂.rtr.obj? .act a)
  := sorry
  /-
  | skipReaction ..,        _,  _ => rfl
  | execReaction _ _ ho hs, hr, hd => 
    hs.preserves_unchanged_actions (
      s₁.rcnOutput_action_dep_only · · (by
        simp [State.rcnOutput'] at ho
        have ⟨_, hcs, ho⟩ := ho
        simp [rcn, hcs, identified_changes_equiv_changes ho]
      ) hr hd
    )
  -/

theorem InstStep.pure_preserves_state {j : ID} : 
  (e : s₁ ⇓ᵢ s₂) → (s₁.rtr.obj? .rcn e.rcn = some r) → (r.isPure) → (s₁.rtr.obj? .stv j = s₂.rtr.obj? .stv j)
  := sorry
  /-
  | skipReaction ..,    _,  _ => rfl
  | execReaction _ _ ho hs, hr, hp =>
    hs.preserves_unchanged_state (
      s₁.rcnOutput_pure · (by
        simp [State.rcnOutput'] at ho
        have ⟨_, hcs, ho⟩ := ho
        simp [rcn, hcs, identified_changes_equiv_changes ho]
      ) hr hp
    )
  -/

-- Note: We can't express the result as `∀ x, c₁.obj? .stv x = c₂.obj? .stv x`,
--       as `c₁`/`c₂` might contain `c` as a (transitively) nested reactor. 
theorem InstStep.preserves_external_state : 
  (e : s₁ ⇓ᵢ s₂) → (s₁.rtr.con? .rcn e.rcn = some c) → 
  (s₁.rtr.obj? .rtr j = some c₁) → (s₂.rtr.obj? .rtr j = some c₂) → (c.id ≠ j) →
  (c₁.state = c₂.state)
  := sorry
  /-
  | skipReaction ..,        _,  _,   _,   _ => by simp_all
  | execReaction _ _ ho hs, hc, hc₁, hc₂, hi => by
    apply hs.preserves_Equiv.nest' hc₁ hc₂ |>.obj?_ext (cmp := .stv)
    intro x hx
    have hm := Reactor.local_mem_exclusive hc₁ (Reactor.con?_to_rtr_obj? hc) hi.symm hx
    have hu := hs.preserves_unchanged_state (
      s₁.rcnOutput_state_local · (by
        simp [State.rcnOutput'] at ho
        have ⟨_, hcs, ho⟩ := ho
        simp [rcn, hcs, identified_changes_equiv_changes ho]
      ) hc hm
    )
    exact hs.preserves_Equiv.eq_obj?_nest hu hc₁ hc₂
  -/

theorem InstStep.eq_rcn_eq_changes {e₁ : s ⇓ᵢ s₁} {e₂ : s ⇓ᵢ s₂} :
  (e₁.rcn = e₂.rcn) → (e₁.op.changes = e₂.op.changes) := by
  intro h
  rw [rcn] at h
  simp [(h ▸ e₁.wfOp) ▸ e₂.wfOp |> Option.some_inj.mp]

theorem InstStep.acyclic_deps : (e : s₁ ⇓ᵢ s₂) → (e.rcn >[s₁.rtr]< e.rcn) :=
  λ h => by cases h <;> exact State.allows_requires_acyclic_deps $ by assumption
    
theorem InstStep.indep_rcns_indep_output :
  (e : s ⇓ᵢ s') → (rcn' >[s.rtr]< e.rcn) → (rcn' ≠ e.rcn) → s.rcnOutput rcn' = s'.rcnOutput rcn' := by
  intro h hi hrne
  have hp := h.exec.preserves_rcns (i := rcn')
  cases ho : s.rtr.obj? .rcn rcn' <;> cases ho' : s'.rtr.obj? .rcn rcn'
  case none.none => simp [State.rcnOutput, ho, ho']
  case' none.some, some.none => simp [hp, ho'] at ho
  case some.some => 
    have ⟨⟨p, a, x, t⟩, hj⟩ := State.rcnInput_iff_obj?.mpr ⟨_, ho⟩
    have ⟨⟨p', a', x', t'⟩, hj'⟩ := State.rcnInput_iff_obj?.mpr ⟨_, ho'⟩
    have H1 : p = p' := by 
      simp [s.rcnInput_ports_def hj ho, s'.rcnInput_ports_def hj' ho']
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
      simp [s.rcnInput_time_def hj, s'.rcnInput_time_def hj', h.exec.preserves_tag]
    simp [H1, H2, H3] at hj
    have ⟨r, hr⟩ := Reactor.contains_iff_obj?.mp h.rtr_contains_rcn
    have ⟨_, hc, _⟩ := Reactor.obj?_to_con?_and_cmp? ho
    have ⟨_, hr', _⟩ := Reactor.obj?_to_con?_and_cmp? hr
    cases hi.ne_rtr_or_pure hrne ho hr hc hr'
    case inl he => 
      have ⟨_, hc', _⟩ := Reactor.obj?_to_con?_and_cmp? ho'
      have hs := State.rcnInput_state_def hj hc
      have hs' := State.rcnInput_state_def hj' hc'
      have hq := h.exec.preserves_Equiv
      have hh := hq.con?_id_eq hc hc'
      have hc := Reactor.con?_to_rtr_obj? hc
      have hc' := Reactor.con?_to_rtr_obj? hc'
      rw [←hh] at hc'
      rw [h.preserves_external_state hr' hc hc' he.symm] at hs
      rw [hs.trans hs'.symm] at hj
      exact State.rcnOutput_congr (hj.trans hj'.symm) hp
    case inr hc =>
      cases hc
      case inl hp' => 
        rw [ho'.symm.trans (h.exec.preserves_rcns ▸ ho)] at ho'
        exact State.rcnOutput_pure_congr hj hj' ho ho' hp'
      case inr hp' => 
        have ⟨_, hco, _⟩ := Reactor.obj?_to_con?_and_cmp? ho
        have ⟨_, hco', _⟩ := Reactor.obj?_to_con?_and_cmp? ho'
        have hs := State.rcnInput_state_def hj hco
        have hs' := State.rcnInput_state_def hj' hco'
        suffices h : x = x' by 
          rw [h] at hj
          exact State.rcnOutput_congr (hj.trans hj'.symm) hp
        rw [hs, hs']
        have he := h.exec.preserves_Equiv
        exact (he.con?_obj_equiv hco hco').obj?_ext (cmp := .stv) (by
          intro j _
          have h := h.pure_preserves_state (j := j) hr hp'
          have hh := he.con?_id_eq hco hco'
          have hco := Reactor.con?_to_rtr_obj? hco
          have hco' := Reactor.con?_to_rtr_obj? hco'
          rw [←hh] at hco'
          exact he.eq_obj?_nest h hco hco' 
        )