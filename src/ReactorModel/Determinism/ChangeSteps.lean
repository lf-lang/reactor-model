import ReactorModel.Determinism.ChangeListEquiv

open Classical

theorem List.filterMap_nil {l : List α} : (l.filterMap f = []) → ∀ a ∈ l, f a = none := by
  sorry

namespace Execution

theorem ChangeStep.preserves_ctx : (s₁ -[rcn:c]→ s₂) → s₁.ctx = s₂.ctx := 
  (by cases · <;> rfl)

theorem ChangeStep.preserves_rcns {i : ID} :
  (s₁ -[rcn:c]→ s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i) :=
  λ h => by cases h <;> simp <;> simp [Reactor.Update.preserves_ne_cmp_or_id (by assumption)]

theorem ChangeStep.preserves_Equiv : (s₁ -[rcn:c]→ s₂) → s₁.rtr ≈ s₂.rtr := by
  intro h
  cases h <;> simp
  case' port h, state h, action h => exact h.preserves_Equiv (by simp)
  
theorem ChangeStep.preserves_unchanged_port {i : ID} :
  (s₁ -[rcn:c]→ s₂) → (∀ v, .port i v ≠ c) → (s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i) := by
  intro h hc 
  cases h <;> simp
  case port i' v _ h =>
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
  case action i' t v _ h =>
    refine Reactor.Update.preserves_ne_cmp_or_id h (.inr ?_) (by simp) (by simp)
    by_contra hi
    specialize hc t v
    rw [hi] at hc
    contradiction
  case' state h, port h => exact Reactor.Update.preserves_ne_cmp_or_id h (.inl $ by simp) (by simp) (by simp)

theorem ChangeStep.preserves_unchanged_state {i : ID} :
  (s₁ -[rcn:c]→ s₂) → (∀ v, .state i v ≠ c) → (s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i) := by
  intro h hc 
  cases h <;> simp
  case state i' v _ h =>
    refine Reactor.Update.preserves_ne_cmp_or_id h (.inr ?_) (by simp) (by simp)
    by_contra hi
    specialize hc v
    rw [hi] at hc
    contradiction
  case' action h, port h => exact Reactor.Update.preserves_ne_cmp_or_id h (.inl $ by simp) (by simp) (by simp)

theorem ChangeStep.preserves_port_role {i : ID} :
  (s₁ -[rcn:c]→ s₂) → (s₁.rtr.obj? .prt i = some p) → (∃ v, s₂.rtr.obj? .prt i = some ⟨v, p.kind⟩) := by
  intro hs ho
  cases hs
  case port j v _ h =>
    have ⟨_, ho', hv⟩ := h.change'
    by_cases hi : i = j
    case pos =>
      exists v
      rw [hi] at ho ⊢
      simp [ho.symm.trans ho' |> Option.some_inj.mp, hv]
    case neg =>
      exists p.val
      simp [←h.preserves_ne_cmp_or_id (cmp' := .prt) (i' := i) (by simp [hi]) (by simp) (by simp), ho]
  all_goals exists p.val
  case' state h, action h => simp [←h.preserves_ne_cmp_or_id (cmp' := .prt) (i' := i) (by simp) (by simp) (by simp), ho]
  all_goals exact ho
  
theorem ChangeStep.port_change_mem_rtr {i : ID} : (s -[rcn:.port i v]→ s') → (∃ p, s.rtr.obj? .prt i = some p) 
  | .port hu => hu.obj?_target

theorem ChangeListStep.preserves_ctx : (s₁ -[rcn:cs]→* s₂) → s₁.ctx = s₂.ctx 
  | .nil .. => rfl
  | .cons h₁₂ h₂₃ => h₁₂.preserves_ctx.trans h₂₃.preserves_ctx

theorem ChangeListStep.preserves_rcns {i : ID} : (s₁ -[rcn:cs]→* s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i)
  | .nil .. => rfl
  | .cons h₁₂ h₂₃ => h₁₂.preserves_rcns.trans h₂₃.preserves_rcns

theorem ChangeListStep.preserves_Equiv : (s₁ -[rcn:cs]→* s₂) → s₁.rtr ≈ s₂.rtr
  | nil .. => .refl
  | cons h hi => h.preserves_Equiv.trans hi.preserves_Equiv

theorem ChangeListStep.preserves_unchanged_ports {i : ID} :
  (s₁ -[rcn:cs]→* s₂) → (∀ v, .port i v ∉ cs) → (s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i)
  | nil ..,    _ => rfl
  | cons h hi, hc => by
    refine (h.preserves_unchanged_port ?_).trans (hi.preserves_unchanged_ports ?_) <;> (
      intro v
      have ⟨_, _⟩ := (not_or ..).mp $ (mt List.mem_cons.mpr) $ hc v
      assumption
    )

theorem ChangeListStep.preserves_unchanged_actions {i : ID} :
  (s₁ -[rcn:cs]→* s₂) → (∀ t v, .action i t v ∉ cs) → (s₁.rtr.obj? .act i = s₂.rtr.obj? .act i)
  | nil ..,    _ => rfl
  | cons h hi, hc => by
    refine (h.preserves_unchanged_action ?_).trans (hi.preserves_unchanged_actions ?_) <;> (
      intro t v
      have ⟨_, _⟩ := (not_or ..).mp $ (mt List.mem_cons.mpr) $ hc t v
      assumption
    )

theorem ChangeListStep.preserves_unchanged_state {i : ID} :
  (s₁ -[rcn:cs]→* s₂) → (∀ v, .state i v ∉ cs) → (s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i)
  | nil ..,    _ => rfl
  | cons h hi, hc => by
    refine (h.preserves_unchanged_state ?_).trans (hi.preserves_unchanged_state ?_) <;> (
      intro v
      have ⟨_, _⟩ := (not_or ..).mp $ (mt List.mem_cons.mpr) $ hc v
      assumption
    )

theorem ChangeListStep.preserves_port_role {i : ID} :
  (s₁ -[rcn:cs]→* s₂) → (s₁.rtr.obj? .prt i = some p) → (∃ v, s₂.rtr.obj? .prt i = some ⟨v, p.kind⟩)
  | nil ..,     ho => ⟨_, ho⟩
  | cons hd tl, ho => by simp [tl.preserves_port_role (hd.preserves_port_role ho).choose_spec]

theorem ChangeListStep.lastSome?_none_preserves_state_value :
  (s₁ -[rcn:cs]→* s₂) → (cs.lastSome? (·.stateValue? i) = none) → (s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i) := by
  intro hs hl 
  have h := (mt List.lastSome?_eq_some_iff.mpr) (Option.eq_none_iff_forall_not_mem.mp hl |> not_exists_of_forall_not)
  exact hs.preserves_unchanged_state (i := i) (by
    intro v hn
    simp at h
    specialize h v (.state i v) hn
    simp [Change.stateValue?] at h
  )

theorem ChangeListStep.last_state_value :
  (s₁ -[rcn:cs]→* s₂) → (cs.lastSome? (·.stateValue? i) = some v) → (s₂.rtr.obj? .stv i = some v)
  | nil ..,                      hl => by simp [List.lastSome?_empty_eq_none] at hl
  | @cons _ _ _ _ hd tl hhd htl, hl => by
    by_cases hc : ∃ w, tl.lastSome? (·.stateValue? i) = some w
    case pos =>
      have ⟨w, hc⟩ := hc
      exact htl.last_state_value ((List.lastSome?_tail hl hc).symm ▸ hc)
    case neg =>
      simp at hc
      have hln := Option.eq_none_iff_forall_not_mem.mpr hc
      simp [←htl.lastSome?_none_preserves_state_value hln]
      have hv := List.lastSome?_head hl hln
      rw [Change.stateValue?_some hv.symm] at hhd
      cases hhd
      case state hu => have ⟨_, _, h⟩ := hu.change'; simp [h]

theorem ChangeListStep.lastSome?_none_preserves_port_value :
  (s₁ -[rcn:cs]→* s₂) → (cs.lastSome? (·.portValue? i) = none) → (s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i) := by
  intro hs hl 
  have h := (mt List.lastSome?_eq_some_iff.mpr) (Option.eq_none_iff_forall_not_mem.mp hl |> not_exists_of_forall_not)
  exact hs.preserves_unchanged_ports (i := i) (by
    intro v hn
    simp at h
    specialize h v (.port i v) hn
    simp [Change.portValue?] at h
  )

theorem ChangeListStep.last_port_value :
  (s₁ -[rcn:cs]→* s₂) → (cs.lastSome? (·.portValue? i) = some v) → (∃ k, s₂.rtr.obj? .prt i = some ⟨v, k⟩)
  | nil ..,                      hl => by simp [List.lastSome?_empty_eq_none] at hl
  | @cons _ _ _ _ hd tl hhd htl, hl => by
    by_cases hc : ∃ w, tl.lastSome? (·.portValue? i) = some w
    case pos =>
      have ⟨w, hc⟩ := hc
      exact htl.last_port_value ((List.lastSome?_tail hl hc).symm ▸ hc)
    case neg =>
      simp at hc
      have hln := Option.eq_none_iff_forall_not_mem.mpr hc
      simp [←htl.lastSome?_none_preserves_port_value hln]
      have hv := List.lastSome?_head hl hln
      rw [Change.portValue?_some hv.symm] at hhd
      cases hhd
      case port hu => have ⟨_, _, h⟩ := hu.change'; simp [h]

theorem ChangeListStep.port_change_mem_rtr {i : ID} : 
  (s -[rcn:cs]→* s') → (.port i v ∈ cs) → (∃ p, s.rtr.obj? .prt i = some p) := by
  intro hs hm
  induction hs
  case nil => contradiction
  case cons hi => 
    cases hm
    case head hs => exact hs.port_change_mem_rtr
    case tail hs _ hm => exact hs.preserves_Equiv.obj?_iff.mpr (hi hm)

theorem ChangeListStep.preserves_actions_at_unchanged_times {i : ID} : 
  (s₁ -[rcn:cs]→* s₂) → (∀ v, .action i t v ∉ cs) → 
  (s₁.rtr.obj? .act i = some a₁) → (s₂.rtr.obj? .act i = some a₂) →
  (∀ m, a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) :=
  sorry

theorem ChangeListStep.equiv_changes_eq_result :
  (s -[rcn₁:cs₁]→* s₁) → (s -[rcn₂:cs₂]→* s₂) → (cs₁ ⋈ cs₂) → s₁ = s₂ := by
  intro h₁ h₂ he
  refine State.ext _ _ ?_ (h₁.preserves_ctx.symm.trans h₂.preserves_ctx)
  have hq := h₁.preserves_Equiv.symm.trans h₂.preserves_Equiv
  apply hq.obj?_ext'
  intro cmp i hnr
  cases cmp <;> simp [←h₁.preserves_rcns, ←h₂.preserves_rcns] at hnr ⊢ <;> clear hnr
  case stv =>
    have hs := he.state i
    cases hc : cs₁.lastSome? (·.stateValue? i)
    case none => simp [←h₁.lastSome?_none_preserves_state_value hc, ←h₂.lastSome?_none_preserves_state_value (hs ▸ hc)]
    case some => simp [h₁.last_state_value hc, h₂.last_state_value (hs ▸ hc)]
  case prt =>
    have hp := he.ports i
    cases hc : cs₁.lastSome? (·.portValue? i)
    case none => simp [←h₁.lastSome?_none_preserves_port_value hc, ←h₂.lastSome?_none_preserves_port_value (hp ▸ hc)]
    case some => 
      have ⟨_, hl₁⟩ := h₁.last_port_value hc
      have ⟨_, hl₂⟩ := h₂.last_port_value (hp ▸ hc)
      cases hc' : s.rtr.obj? .prt i
      case none => 
        have ⟨_, _, hm₁, hm₂⟩ := List.lastSome?_eq_some_iff.mp ⟨_, hc⟩
        rw [Change.portValue?_some hm₂] at hm₁
        have ⟨_, hm₃⟩ := h₁.port_change_mem_rtr hm₁
        have := hm₃.symm.trans hc'
        contradiction
      case some =>
        have ⟨_, hr₁⟩ := h₁.preserves_port_role hc'
        have ⟨_, hr₂⟩ := h₂.preserves_port_role hc'
        simp [hl₁, hl₂]
        simp [hr₁] at hl₁
        simp [hr₂] at hl₂
        exact hl₁.right.symm.trans hl₂.right
  case act =>
    cases hc₁ : s₁.rtr.obj? .act i <;> cases hc₂ : s₂.rtr.obj? .act i <;> simp
    case none.some =>
      have ⟨_, hc₁'⟩ := hq.obj?_iff.mpr ⟨_, hc₂⟩ 
      have := hc₁.symm.trans hc₁'
      contradiction
    case some.none =>
      have ⟨_, hc₂'⟩ := hq.obj?_iff.mp ⟨_, hc₁⟩ 
      have := hc₂.symm.trans hc₂'
      contradiction
    case some.some a₁ a₂ => 
      refine Finmap.ext _ _ ?_
      intro g
      have ha := he.actions i g.time
      generalize hacs : cs₁.filterMap (·.actionValue? i g.time) = acs
      induction acs
      case nil =>
        have hm₁ : ∀ v, .action i g.time v ∉ cs₁ := by 
          intro v
          by_contra hc
          have hc' := List.filterMap_nil hacs _ hc
          simp [Change.actionValue?] at hc'
        have hm₂ : ∀ v, .action i g.time v ∉ cs₂ := by 
          rw [hacs] at ha
          intro v
          by_contra hc
          have hc' := List.filterMap_nil ha.symm _ hc
          simp [Change.actionValue?] at hc'
        have ⟨_, hc⟩ := h₁.preserves_Equiv.obj?_iff.mpr ⟨_, hc₁⟩
        simp [←h₁.preserves_actions_at_unchanged_times hm₁ hc hc₁ g.microstep,
              ←h₂.preserves_actions_at_unchanged_times hm₂ hc hc₂ g.microstep]
      case cons hd tl hi =>
        -- TODO: `hi` can't be used (cf. `hacs`).
        --       Does something need to be generalized?
        sorry
      
  