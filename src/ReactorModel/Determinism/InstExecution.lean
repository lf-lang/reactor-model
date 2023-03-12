import ReactorModel.Determinism.InstStep

open Classical

namespace Execution
namespace InstExecution

open State (Closed)

theorem rcns_unprocessed : 
  (e : s₁ ⇓ᵢ* s₂) → ∀ rcn ∈ e.rcns, rcn ∉ s₁.progress := by
  intro h rcn hr
  induction h
  case refl => sorry
    -- simp [rcns] at hr
    -- have h := h.rcn_unprocessed
    -- simp [InstStep.rcn] at h
    -- simp [hr, h]
  case trans hi =>
    cases List.mem_cons.mp hr
    case inl h _ hc => 
      simp [rcns] at hc
      have h := h.rcn_unprocessed
      simp [InstStep.rcn, ←hc] at h
      exact h
    case inr h₁ _ h => 
      specialize hi h
      exact (not_or.mp $ (mt h₁.mem_progress.mpr) hi).right

theorem rcns_nodup : (e : s₁ ⇓ᵢ* s₂) → List.Nodup e.rcns
  | refl => List.nodup_nil
  | trans h₁ h₂ => List.nodup_cons.mpr $ ⟨(mt $ h₂.rcns_unprocessed _) $ not_not.mpr h₁.self_progress, h₂.rcns_nodup⟩

theorem ops_nodup : (e : s₁ ⇓ᵢ* s₂) → List.Nodup e.ops := by
  intro e
  induction e
  case refl => exact List.nodup_nil
  case trans hd tl h =>
    simp [ops, List.nodup_cons, h]
    by_contra hm
    have h' := tl.rcns_unprocessed hd.op.rcn
    simp [rcns, List.mem_map] at h'
    specialize h' hd.op hm rfl
    sorry -- simp [hd.exec.ctx_adds_rcn, State.mem_record_progress_iff] at h'

theorem mem_progress :
  (e : s₁ ⇓ᵢ* s₂) → ∀ rcn, rcn ∈ s₂.progress ↔ rcn ∈ e.rcns ∨ rcn ∈ s₁.progress := by
  intro h rcn
  induction h
  case refl => sorry -- simp [InstStep.rcn, rcns, List.mem_singleton, h.mem_progress]
  case trans h₁ h₂ hi => 
    constructor <;> intro hc 
    case mp =>
      cases hi.mp hc with
      | inl h => exact .inl $ List.mem_cons_of_mem _ h
      | inr h => 
        by_cases hc : rcn ∈ (h₁.rcn :: h₂.rcns)
        case pos => exact .inl hc
        case neg => exact .inr $ (h₁.mem_progress.mp h).resolve_left $ List.ne_of_not_mem_cons hc
    case mpr =>
      cases hc with
      | inl h => 
        cases (List.mem_cons ..).mp h with
        | inl h => exact hi.mpr $ .inr (h ▸ h₁.self_progress)
        | inr h => exact hi.mpr $ .inl h
      | inr h => exact hi.mpr $ .inr $ h₁.monotonic_progress h

-- Corollary of `InstExecution.mem_progress`.
theorem self_progress : (e : s₁ ⇓ᵢ* s₂) → ∀ rcn ∈ e.rcns, rcn ∈ s₂.progress := 
  λ h _ hm => (h.mem_progress _).mpr $ .inl hm
  
theorem eq_context_processed_rcns_perm : 
  (e₁ : s ⇓ᵢ* s₁) → (e₂ : s ⇓ᵢ* s₂) → (s₁.tag = s₂.tag) → (s₁.progress = s₂.progress) → e₁.rcns ~ e₂.rcns := by
  intro h₁ h₂ ht hp
  apply (List.perm_ext h₁.rcns_nodup h₂.rcns_nodup).mpr
  intro rcn
  by_cases hc : rcn ∈ s.progress
  case pos =>
    have h₁ := (mt $ h₁.rcns_unprocessed rcn) (not_not.mpr hc)
    have h₂ := (mt $ h₂.rcns_unprocessed rcn) (not_not.mpr hc)
    exact iff_of_false h₁ h₂ 
  case neg =>
    constructor <;> intro hm
    case mp => 
      have h := h₁.self_progress _ hm
      sorry
      -- rw [State.progress, he] at h
      -- exact ((h₂.mem_progress _).mp h).resolve_right hc
    case mpr =>
      have h := h₂.self_progress _ hm
      sorry
      -- rw [State.progress, ←he] at h
      -- exact ((h₁.mem_progress _).mp h).resolve_right hc

/-theorem rcn_list_cons : (e : s₁ ⇓ᵢ+ s₂) → ∃ hd tl, e.rcns = hd :: tl :=
  (by cases · <;> simp [rcns])
-/

theorem to_ChangeListStep :
  (e : s₁ ⇓ᵢ* s₂) → (s₁ -[e.changes]→* { s₁ with rtr := s₂.rtr}) := by
  intro e
  induction e
  case refl => exact .nil
  case trans s₁ sₘ s₂ e₁ e₂ hi => 
    have h := e₁.exec.to_ChangeListStep
    simp [changes]
    have hs := ChangeListStep.append h hi rfl
    exact hs

/-
theorem rcns_singleton (e : s₁ ⇓ᵢ+ s₂) :
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

theorem mem_ops_split (e : s₁ ⇓ᵢ* s₂) :
  (op ∈ e.ops) → 
  ∃ (sₘ₁ : _) (sₘ₂ : _) (e₁ : s₁ ⇓ᵢ* sₘ₁) (eₘ : sₘ₁ ⇓ᵢ sₘ₂) (e₂ : sₘ₂ ⇓ᵢ* s₂), 
  (e = e₁ ++ eₘ ++ e₂) ∧ (eₘ.op = op) :=
  sorry
-/

theorem same_rcns_same_ops (e₁ : s ⇓ᵢ* s₁) (e₂ : s ⇓ᵢ* s₂) :
  (e₁.rcns ~ e₂.rcns) → (e₁.ops ~ e₂.ops) := by
  intro hp
  simp [List.perm_ext e₁.ops_nodup e₂.ops_nodup]
  intro op
  suffices H : ∀ {s₁ s₂} (e₁ : s ⇓ᵢ* s₁) (e₂ : s ⇓ᵢ* s₂), (e₁.rcns ~ e₂.rcns) → ∀ {op}, op ∈ e₁.ops → op ∈ e₂.ops 
    from ⟨H e₁ e₂ hp, H e₂ e₁ hp.symm⟩
  intro s₁ s₂ e₁ e₂ hp op h
  sorry
  /-
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
  -/

/-
theorem port_change_to_op {e : s₁ ⇓ᵢ* s₂} {i : Fin e.changes.length} :
  (e.changes[i].obj = .port k p v) → 
  ∃ op rcn, (op ∈ e.ops) ∧ (⟨op.rcn, .port k p v⟩ ∈ op.changes) ∧ (s₁.rtr[.rcn][op.rcn] = some rcn) ∧ (.port k p ∈ rcn.deps .out) := by
  sorry

theorem state_change_to_op {e : s₁ ⇓ᵢ* s₂} {i : Fin e.changes.length} :
  (e.changes[i].obj = .state a v) → 
  ∃ op, (op ∈ e.ops) ∧ (⟨op.rcn, .state a v⟩ ∈ op.changes) ∧ (s₁.rtr[.stv][a]& = s₁.rtr[.rcn][op.rcn]&) := by
  sorry

theorem Reactor.uniqueInputs' {rtr : Reactor} {iₚ i₁ i₂ : ID} :
  (iₚ ∈ rtr[.inp].ids) → (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → 
  (.port .in iₚ ∈ rcn₁.deps .out) → .port .in iₚ ∉ rcn₂.deps .out := by
  sorry

theorem Reactor.out_port_out_dep_eq_parent {rtr : Reactor} {iₚ iᵣ : ID} :
  (iₚ ∈ rtr[.out].ids) → (rtr[.rcn][iᵣ] = some rcn) → (.port .out iₚ ∈ rcn.deps .out) → 
  (rtr[.out][iₚ]& = rtr[.rcn][iᵣ]&) := by
  sorry

theorem op_eq_rcn_eq {e : s₁ ⇓ᵢ* s₂} :
  (op₁ ∈ e.ops) → (op₂ ∈ e.ops) → (op₁.rcn = op₂.rcn) → (op₁ = op₂) := by
  sorry

theorem ops_respect_dependencies {i₁ i₂ : Nat} : 
  (e : s₁ ⇓ᵢ* s₂) →
  (e.ops[i₁]? = some op₁) → (e.ops[i₂]? = some op₂) → 
  (op₁.rcn >[s₁.rtr] op₂.rcn) → (i₁ < i₂) := by
  sorry

theorem changes_order_to_ops_internal_order {e : s₁ ⇓ᵢ* s₂} {ic : Fin e.changes.length} {io : Nat} :
  (e.changes[ic].obj = c) →
  (∀ j : Fin e.changes.length, (j > ic) → e.changes[j].obj.stateValue? i = none) → 
  (op ∈ e.ops) →
  (op.changes[io]? = some ⟨op.rcn, c⟩) →
  (∀ j c', (j > io) → (op.changes[j]? = some c') → c'.obj.stateValue? i = none) := by
  sorry

theorem same_ops_ChangeEquiv_ports {e₁ : s ⇓ᵢ* s₁} {e₂ : s ⇓ᵢ* s₂} :
  (e₁.ops ~ e₂.ops) → (∀ k i, e₁.changes.lastSome? (·.obj.portValue? k i) = e₂.changes.lastSome? (·.obj.portValue? k i)) := by
  intro ho k i
  /-cases hc : e₁.changes.lastSome? (·.obj.portValue? i)
    case none =>
      have := (mt List.lastSome?_eq_some_iff.mpr) (Option.eq_none_iff_forall_not_mem.mp hc |> not_exists.mpr)
      sorry -- ...
    case some -/
    
  -- lets assume both sides are some just to get to the core of the argument rn:
  have ⟨v₁, hc₁⟩ : ∃ v, e₁.changes.lastSome? (·.obj.portValue? k i) = some v := sorry
  have ⟨v₂, hc₂⟩ : ∃ v, e₂.changes.lastSome? (·.obj.portValue? k i) = some v := sorry
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
  sorry
  /-
  have ⟨p, hp⟩ : ∃ p, s.rtr[.prt][i] = some p := sorry
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
  -/

theorem List.get?_eq_getElem? (l : List α) (i : Nat) : l.get? i = l[i]? := sorry

theorem List.last_with_property_unique {l : List α} {p : α → Prop} {i₁ i₂ : Nat} :
  (l[i₁]? = some a₁) → (p a₁) → (∀ j a, (j > i₁) → (l[j]? = some a) → ¬p a) →
  (l[i₂]? = some a₂) → (p a₂) → (∀ j a, (j > i₂) → (l[j]? = some a) → ¬p a) →
  i₁ = i₂ :=
  sorry

/-
theorem Reactor.orderable_impure {rtr : Reactor} {i₁ i₂ : ID} :
  (rtr[.rcn][i₁] = some rcn₁) → (¬rcn₁.Pure) → 
  (rtr[.rcn][i₂] = some rcn₂) → (¬rcn₂.Pure) →
  (rtr[.rcn][i₁]& = rtr[.rcn][i₂]&) → (i₁ ≠ i₂) → 
  Reactor.Orderable rtr rcn₁ rcn₂ :=
  sorry
-/

theorem state_change_mem_op_rcn_eq_con? {e : s₁ ⇓ᵢ* s₂} :
  (op ∈ e.ops) → (⟨op.rcn, .state i v⟩ ∈ op.changes) → 
  (s₁.rtr[.stv][i]& = s₁.rtr[.rcn][op.rcn]&)
  := sorry

theorem state_change_mem_op_rcn_impure {e : s₁ ⇓ᵢ* s₂} :
  (op ∈ e.ops) → (⟨op.rcn, .state i v⟩ ∈ op.changes) →
  ∃ rcn, (s₁.rtr[.rcn][op.rcn] = some rcn) ∧ (¬rcn.Pure) := sorry

theorem same_ops_ChangeEquiv_state {e₁ : s ⇓ᵢ* s₁} {e₂ : s ⇓ᵢ* s₂} :
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
    sorry 
    /-
    have hio₁ := changes_order_to_ops_internal_order hi₁ hj₁ hom₁ H1
    have hio₂ := changes_order_to_ops_internal_order hi₂ hj₂ hom₂ H2
    set c₁ : Identified Change := { id := op₁.rcn, obj := .state i v₁ }
    set c₂ : Identified Change := { id := op₂.rcn, obj := .state i v₂ }
    replace hio₁ : ∀ (j : ℕ) (c' : Identified Change), j > X1 → (Operation.changes op₁)[j]? = some c' → ¬(c'.obj.stateValue? i).isSome := by
      intro j c' hj hc
      simp [hio₁ j c' hj hc]
    replace hio₂ : ∀ (j : ℕ) (c' : Identified Change), j > X2 → (Operation.changes op₂)[j]? = some c' → ¬(c'.obj.stateValue? i).isSome := by
      intro j c' hj hc
      simp [hio₂ j c' hj hc]
    rw [←heo] at H2 hio₂
    have H : X1 = X2 := List.last_with_property_unique 
      H1 (by simp [Change.stateValue?] : (c₁.obj.stateValue? i).isSome) hio₁ 
      H2 (by simp [Change.stateValue?] : (c₂.obj.stateValue? i).isSome) hio₂
    rw [H] at H1
    injection H1.symm.trans H2 with H3
    injection H3 with _ H4
    injection H4 with _ H5
    rw [H5]
    -/
  case neg =>
    exfalso
    -- The op₁.rcn and op₂.rcn must live in the same reactor, as they both write to the same state variable i.
    have H1 := (e₁.state_change_mem_op_rcn_eq_con? hom₁ hcm₁).symm.trans (e₂.state_change_mem_op_rcn_eq_con? hom₂ hcm₂)
    -- Since the reactions write to a state variable, they are not pure.
    have ⟨rcn₁, hor₁, hp₁⟩ := e₁.state_change_mem_op_rcn_impure hom₁ hcm₁
    have ⟨rcn₂, hor₂, hp₂⟩ := e₂.state_change_mem_op_rcn_impure hom₂ hcm₂
    -- There must exist a dependency relation between the two reactions.
    have hd : (op₁.rcn >[s.rtr] op₂.rcn) ∨ (op₂.rcn >[s.rtr] op₁.rcn) := by
      by_cases hm : rcn₁.Mutates ↔ rcn₂.Mutates
      case pos => sorry
        -- cases s.rtr.orderability (Reactor.orderable_impure hor₁ hp₁ hor₂ hp₂ H1 hr)
        -- case inl hp => exact .inr (Dependency.prio H1.symm hor₂ hor₁ hm.symm hp)
        -- case inr hp => exact .inl (Dependency.prio H1      hor₁ hor₂ hm      hp)
      case neg =>
        rw [not_iff] at hm
        by_cases hm₁ : rcn₁.Mutates
        case pos =>
          have hm₂ := mt hm.mpr $ not_not.mpr hm₁
          simp [Reaction.Mutates] at hm₂
          sorry -- exact .inl (Dependency.mutNorm H1 hor₁ hor₂ hm₁ hm₂)
        case neg =>
          have hm₂ := hm.mp hm₁
          simp [Reaction.Mutates] at hm₁
          sorry -- exact .inr (Dependency.mutNorm H1.symm hor₂ hor₁ hm₂ hm₁)
    sorry
    -- Thus, within the list of ops, the ordering between the ops is the same within e₁.ops and e₂.ops
    -- (because execution respects dependency order: `ops_respect_dependencies`).
    -- Thus (wlog. assuming op₁ must appear before op₂) e₁.ops must also contain op₂ (by `ho`) somewhere after op₁. 
    -- Thus the assumption hj₂ is false.

theorem same_ops_ChangeEquiv_actions {e₁ : s ⇓ᵢ* s₁} {e₂ : s ⇓ᵢ* s₂} :
  (e₁.ops ~ e₂.ops) → (∀ i t, e₁.changes.filterMap (·.obj.actionValue? i t) = e₂.changes.filterMap (·.obj.actionValue? i t)) := by
  sorry

theorem same_rcns_ChangeEquiv {e₁ : s ⇓ᵢ* s₁} {e₂ : s ⇓ᵢ* s₂} : 
  (e₁.rcns ~ e₂.rcns) → (e₁.changes ⋈ e₂.changes) := by
  intro hr
  have ho := e₁.same_rcns_same_ops e₂ hr
  exact {
    ports := same_ops_ChangeEquiv_ports ho,
    state := same_ops_ChangeEquiv_state ho,
    actions := same_ops_ChangeEquiv_actions ho
  }

-/

protected theorem deterministic : 
  (s ⇓ᵢ* s₁) → (s ⇓ᵢ* s₂) → (s₁.tag = s₂.tag) → (s₁.progress = s₂.progress) → s₁ = s₂ := by
  intro e₁ e₂ ht hp
  refine State.ext _ _ ?_ ht hp
  have hp := e₁.eq_context_processed_rcns_perm e₂ ht hp
  -- have he := e₁.same_rcns_ChangeEquiv hp
  injection e₁.to_ChangeListStep.equiv_changes_deterministic e₂.to_ChangeListStep sorry
    









theorem tag_eq : (s₁ ⇓ᵢ* s₂) → s₁.tag = s₂.tag
  | refl => rfl
  | trans e e' => e.exec.preserves_tag.trans e'.tag_eq

theorem rcns_trans_eq_cons (e₁ : s ⇓ᵢ s₁) (e₂ : s₁ ⇓ᵢ* s₂) : 
    (trans e₁ e₂).rcns = e₁.rcn :: e₂.rcns := by
  simp [rcns, InstStep.rcn]

theorem progress_eq : (e : s₁ ⇓ᵢ* s₂) → s₂.progress = s₁.progress ∪ { i | i ∈ e.rcns }
  | refl => by simp [rcns]
  | trans e e' => by 
    simp [e.progress_eq ▸ e'.progress_eq, rcns_trans_eq_cons]
    apply Set.insert_union'

theorem mem_rcns_not_mem_progress (e : s₁ ⇓ᵢ* s₂) (h : rcn ∈ e.rcns) : rcn ∉ s₁.progress := by
  induction e
  case refl => contradiction
  case trans e e' hi =>
    cases e'.rcns_trans_eq_cons e ▸ h
    case head   => exact e.rcn_unprocessed
    case tail h => exact mt e.monotonic_progress (hi h)
      
theorem mem_rcns_iff (e : s₁ ⇓ᵢ* s₂) : rcn ∈ e.rcns ↔ (rcn ∈ s₂.progress ∧ rcn ∉ s₁.progress) := by
  simp [e.progress_eq, s₁.mem_record'_progress_iff e.rcns rcn, or_and_right]
  exact e.mem_rcns_not_mem_progress

theorem preserves_rcns : (s₁ ⇓ᵢ* s₂) → s₁.rtr[.rcn] = s₂.rtr[.rcn]
  | refl => rfl
  | trans e e' => e.exec.preserves_rcns ▸ e'.preserves_rcns

end InstExecution
end Execution