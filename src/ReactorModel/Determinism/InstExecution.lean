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

theorem InstExecution.port_change_to_op {e : s₁ ⇓ᵢ+ s₂} {i : Fin e.changes.length} :
  (e.changes[i].obj = .port p v) → 
  ∃ op rcn, (op ∈ e.ops) ∧ (⟨op.rcn, .port p v⟩ ∈ op.changes) ∧ (s₁.rtr.obj? .rcn op.rcn = some rcn) ∧ (p ∈ rcn.deps .out) := by
  sorry

theorem InstExecution.state_change_to_op {e : s₁ ⇓ᵢ+ s₂} {i : Fin e.changes.length} :
  (e.changes[i].obj = .state a v) → 
  ∃ op, (op ∈ e.ops) ∧ (⟨op.rcn, .state a v⟩ ∈ op.changes) ∧ (s₁.rtr.con? .stv a = s₁.rtr.con? .rcn op.rcn) := by
  sorry

theorem Reactor.uniqueInputs' {rtr : Reactor} {iₚ i₁ i₂ : ID} :
  (rtr.obj? .prt iₚ = some p) → (p.kind = .in) →
  (rtr.obj? .rcn i₁ = some rcn₁) → (rtr.obj? .rcn i₂ = some rcn₂) → (i₁ ≠ i₂) → 
  (iₚ ∈ rcn₁.deps .out) → iₚ ∉ rcn₂.deps .out := by
  sorry

theorem Reactor.out_port_out_dep_eq_parent {rtr : Reactor} {iₚ iᵣ : ID} :
  (rtr.obj? .prt iₚ = some p) → (p.kind = .out) →
  (rtr.obj? .rcn iᵣ = some rcn) → (iₚ ∈ rcn.deps .out) → 
  (rtr.con? .prt iₚ = rtr.con? .rcn iᵣ) := by
  sorry

theorem InstExecution.op_eq_rcn_eq {e : s₁ ⇓ᵢ+ s₂} :
  (op₁ ∈ e.ops) → (op₂ ∈ e.ops) → (op₁.rcn = op₂.rcn) → (op₁ = op₂) := by
  sorry

theorem InstExecution.ops_respect_dependencies {i₁ i₂ : Nat} : 
  (e : s₁ ⇓ᵢ+ s₂) →
  (e.ops[i₁]? = some op₁) → (e.ops[i₂]? = some op₂) → 
  (op₁.rcn >[s₁.rtr] op₂.rcn) → (i₁ < i₂) := by
  sorry

theorem InstExecution.changes_order_to_ops_internal_order {e : s₁ ⇓ᵢ+ s₂} {ic : Fin e.changes.length} {io : Nat} :
  (e.changes[ic].obj = c) →
  (∀ j : Fin e.changes.length, (j > ic) → e.changes[j].obj.stateValue? i = none) → 
  (op ∈ e.ops) →
  (op.changes[io]? = some ⟨op.rcn, c⟩) →
  (∀ j c', (j > io) → (op.changes[j]? = some c') → c'.obj.stateValue? i = none) := by
  sorry

theorem InstExecution.same_ops_ChangeListEquiv_ports {e₁ : s ⇓ᵢ+ s₁} {e₂ : s ⇓ᵢ+ s₂} :
  (e₁.ops ~ e₂.ops) → (∀ i, e₁.changes.lastSome? (·.obj.portValue? i) = e₂.changes.lastSome? (·.obj.portValue? i)) := by
  intro ho i
  /-cases hc : e₁.changes.lastSome? (·.obj.portValue? i)
    case none =>
      have := (mt List.lastSome?_eq_some_iff.mpr) (Option.eq_none_iff_forall_not_mem.mp hc |> not_exists.mpr)
      sorry -- ...
    case some -/
    
  -- lets assume both sides are some just to get to the core of the argument rn:
  have ⟨v₁, hc₁⟩ : ∃ v, e₁.changes.lastSome? (·.obj.portValue? i) = some v := sorry
  have ⟨v₂, hc₂⟩ : ∃ v, e₂.changes.lastSome? (·.obj.portValue? i) = some v := sorry
  rw [hc₁, hc₂]

  have ⟨i₁, hi₁, hj₁⟩ := List.lastSome?_eq_some hc₁
  have ⟨i₂, hi₂, hj₂⟩ := List.lastSome?_eq_some hc₂
  replace hi₁ := Change.portValue?_some hi₁
  replace hi₂ := Change.portValue?_some hi₂

  have ⟨op₁, rcn₁, hom₁, hcm₁, ho₁, hd₁⟩ := e₁.port_change_to_op hi₁
  have ⟨op₂, rcn₂, hom₂, hcm₂, ho₂, hd₂⟩ := e₂.port_change_to_op hi₂

  -- 1. show that (.port i v₁) and (.port i v₂) must live in the same op
  -- 2. show that they must be the same change, by hj₁/hj₂

  -- if port i is an input port, there can be at most one reaction that writes to it
  -- if port i is an output port, if there exist multiple ports connected to it, there must be an order on them
  -- lets assume i is a valid port 
  have ⟨p, hp⟩ : ∃ p, s.rtr.obj? .prt i = some p := sorry
  cases hk : p.kind
  case «in» =>
    have hr : op₁.rcn = op₂.rcn := by
      by_contra h
      exact absurd hd₂ (Reactor.uniqueInputs' hp hk ho₁ ho₂ h hd₁)
    have heo := e₁.op_eq_rcn_eq hom₁ (ho.mem_iff.mpr hom₂) hr
    sorry -- step 1 complete for this case
  case out =>
    by_cases hr : op₁.rcn = op₂.rcn
    case pos =>
      have heo := e₁.op_eq_rcn_eq hom₁ (ho.mem_iff.mpr hom₂) hr
      sorry -- step 1 complete for this case
    case neg =>
      have h₁ := Reactor.out_port_out_dep_eq_parent hp hk ho₁ hd₁
      have h₂ := Reactor.out_port_out_dep_eq_parent hp hk ho₂ hd₂
      have h := h₁.symm.trans h₂
      -- establish that there is a dependency between rcn₁ and rcn₂:
      -- this could be by .prio, or .mutNorm.
      have hd : True := sorry
      sorry

theorem List.get?_eq_getElem? (l : List α) (i : Nat) : l.get? i = l[i]? := sorry

theorem InstExecution.same_ops_ChangeListEquiv_state {e₁ : s ⇓ᵢ+ s₁} {e₂ : s ⇓ᵢ+ s₂} :
  (e₁.ops ~ e₂.ops) → (∀ i, e₁.changes.lastSome? (·.obj.stateValue? i) = e₂.changes.lastSome? (·.obj.stateValue? i)) := by
  intro ho i

  have ⟨v₁, hc₁⟩ : ∃ v, e₁.changes.lastSome? (·.obj.stateValue? i) = some v := sorry
  have ⟨v₂, hc₂⟩ : ∃ v, e₂.changes.lastSome? (·.obj.stateValue? i) = some v := sorry
  rw [hc₁, hc₂]

  have ⟨i₁, hi₁, hj₁⟩ := List.lastSome?_eq_some hc₁
  have ⟨i₂, hi₂, hj₂⟩ := List.lastSome?_eq_some hc₂
  replace hi₁ := Change.stateValue?_some hi₁
  replace hi₂ := Change.stateValue?_some hi₂

  have ⟨op₁, hom₁, hcm₁, hc₁⟩ := e₁.state_change_to_op hi₁
  have ⟨op₂, hom₂, hcm₂, hc₂⟩ := e₂.state_change_to_op hi₂

  by_cases hr : op₁.rcn = op₂.rcn 
  case pos =>
    have heo := e₁.op_eq_rcn_eq hom₁ (ho.mem_iff.mpr hom₂) hr
    have ⟨X1, H1⟩ := List.mem_iff_get?.mp hcm₁; rw [List.get?_eq_getElem?] at H1
    have ⟨X2, H2⟩ := List.mem_iff_get?.mp hcm₂; rw [List.get?_eq_getElem?] at H2
    have hio₁ := changes_order_to_ops_internal_order hi₁ hj₁ hom₁ H1
    have hio₂ := changes_order_to_ops_internal_order hi₂ hj₂ hom₂ H2
    rw [←heo] at H2
    have H : X1 = X2 := sorry -- by hio₁ and hio₂
    rw [H] at H1
    injection H1.symm.trans H2 with H3
    injection H3 with _ H4
    injection H4 with _ H5
    rw [H5]
  case neg =>
    exfalso
    sorry
    -- The op₁.rcn and op₂.rcn must live in the same reactor, as they both write to the same state variable i.
    -- Since they write to a state variable, they are also not pure.
    -- There must exist a dependency relation between the two.
    -- Thus, within the list of ops, the ordering between the ops is the same within e₁.ops and e₂.ops
    -- (because execution respects dependency order: `ops_respect_dependencies`).
    -- Thus (wlog. assuming op₁ must appear before op₂) e₁.ops must also contain op₂ (by `ho`) somewhere after op₁. 
    -- Thus the assumption hj₂ is false.

theorem InstExecution.same_ops_ChangeListEquiv_actions {e₁ : s ⇓ᵢ+ s₁} {e₂ : s ⇓ᵢ+ s₂} :
  (e₁.ops ~ e₂.ops) → (∀ i t, e₁.changes.filterMap (·.obj.actionValue? i t) = e₂.changes.filterMap (·.obj.actionValue? i t)) := by
  sorry

theorem InstExecution.same_rcns_ChangeListEquiv {e₁ : s ⇓ᵢ+ s₁} {e₂ : s ⇓ᵢ+ s₂} : 
  (e₁.rcns ~ e₂.rcns) → (e₁.changes ⋈ e₂.changes) := by
  intro hr
  have ho := e₁.same_rcns_same_ops e₂ hr
  exact {
    ports := same_ops_ChangeListEquiv_ports ho,
    state := same_ops_ChangeListEquiv_state ho,
    actions := same_ops_ChangeListEquiv_actions ho
  }

protected theorem InstExecution.deterministic : 
  (s ⇓ᵢ+ s₁) → (s ⇓ᵢ+ s₂) → (s₁.ctx = s₂.ctx) → s₁ = s₂ := by
  intro e₁ e₂ hc
  refine State.ext _ _ ?_ hc
  have hp := e₁.eq_ctx_processed_rcns_perm e₂ hc
  have he := e₁.same_rcns_ChangeListEquiv hp
  injection e₁.to_ChangeListStep.equiv_changes_eq_result e₂.to_ChangeListStep he
  assumption
    
    
      