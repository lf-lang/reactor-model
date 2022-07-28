import ReactorModel.Determinism.ChangeListEquiv

open Classical

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
  
theorem schedule_preserves_unchanged_time :
  (t ≠ t') → a ⟨t', m⟩ = (schedule a t v) ⟨t', m⟩ := by
  intro h 
  unfold schedule
  split
  all_goals
    apply Eq.symm
    apply Finmap.update_ne
    simp [h]

theorem schedule_time_inj :
  (∀ m, a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) → (schedule a₁ t v) ⟨t, m⟩ = (schedule a₂ t v) ⟨t, m⟩ := by
  intro h
  unfold schedule
  cases a₁.ids.filter (·.time = t) |>.max <;>
  cases a₂.ids.filter (·.time = t) |>.max
  case' none.none, none.some =>
    cases m
    case zero => simp [Finmap.update_self]
    case succ => simp [Finmap.update_ne, h]
  case' some.some m₁ _, some.none m₁ =>
    simp
    by_cases hm : m₁.microstep + 1 = m
    case pos => simp [hm, Finmap.update_self]
    case neg => 
      have hm' : Time.Tag.mk t (m₁.microstep + 1) ≠ ⟨t, m⟩ := by simp [hm]
      simp [Finmap.update_ne _ hm', h]

theorem ChangeStep.preserves_action_at_unchanged_times {i : ID} : 
  (s₁ -[rcn:c]→ s₂) → (∀ v, .action i t v ≠ c) → 
  (s₁.rtr.obj? .act i = some a₁) → (s₂.rtr.obj? .act i = some a₂) →
  (∀ m, a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) := by
  intro hs hc ho₁ ho₂ m
  cases hs
  case action i' t' v' σ₂ h =>
    by_cases hi : i = i'
    case neg =>
      rw [h.preserves_ne_cmp_or_id (cmp' := .act) (.inr hi) (by simp) (by simp)] at ho₁
      simp [ho₁] at ho₂
      simp [ho₂]
    case pos =>
      have ht : t ≠ t' := by     
        by_contra ht
        rw [hi, ht] at hc
        have := hc v'
        contradiction
      have ⟨_, hv₁, hv₂⟩ := h.change'
      simp [←hi, ho₁] at hv₁
      simp [←hi, ho₂] at hv₂
      simp [hv₁, hv₂]
      exact schedule_preserves_unchanged_time ht.symm
  case' port h, state h =>
    have ha := h.preserves_ne_cmp_or_id (cmp' := .act) (i' := i) (by simp) (by simp) (by simp)
    simp [ho₁, ho₂] at ha
    simp [ha]
  all_goals
    simp [ho₁] at ho₂
    simp [ho₂]

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
  (∀ m, a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) := by
  intro hs hc ha₁ ha₂ m  
  induction hs generalizing a₁ a₂
  case nil =>
    simp [ha₁] at ha₂
    simp [ha₂]  
  case cons hd _ tl hs₁₂ _ hi =>
    have ⟨_, haₘ⟩ := hs₁₂.preserves_Equiv.obj?_iff.mp ⟨_, ha₁⟩
    have hhd : ∀ v, .action i t v ≠ hd := by 
      intro v
      exact mt List.mem_cons.mpr (hc v) |> (not_or _ _).mp |>.left 
    have htl : ∀ v, .action i t v ∉ tl := by 
      intro v
      exact mt List.mem_cons.mpr (hc v) |> (not_or _ _).mp |>.right
    simp [hs₁₂.preserves_action_at_unchanged_times hhd ha₁ haₘ m, hi htl haₘ ha₂]

theorem ChangeListStep.split :
  (s₁ -[rcn: cs ++ cs']→* s₃) → ∃ s₂, (s₁ -[rcn:cs]→* s₂) ∧ (s₂ -[rcn:cs']→* s₃) := by
  intro h
  generalize hg : cs ++ cs' = l
  rw [hg] at h
  induction h generalizing cs cs'
  case nil s₁ =>
    have ⟨h, h'⟩ := List.append_eq_nil.mp hg
    rw [h, h']
    exact ⟨s₁, .nil, .nil⟩
  case cons s₁ _ hd _ tl h₁₂ _ hi =>
    cases cs
    case nil =>
      have ⟨_, hi₁, hi₂⟩ := @hi [] tl rfl
      cases hi₁
      simp at hg
      rw [hg]
      exact ⟨_, ⟨.nil, .cons h₁₂ hi₂⟩⟩
    case cons hd' tl' =>
      simp at hg
      rw [hg.left]
      have ⟨_, hi₁, hi₂⟩ := hi hg.right
      exact ⟨_, ⟨.cons h₁₂ hi₁, hi₂⟩⟩

theorem ChangeListStep.singleton :
  (s₁ -[rcn:[c]]→* s₂) → (s₁ -[rcn:c]→ s₂) := by
  intro h
  cases h
  case cons h h' =>
    cases h'
    exact h

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
    cases ha₁ : s₁.rtr.obj? .act i <;> cases ha₂ : s₂.rtr.obj? .act i <;> simp
    case none.some =>
      have ⟨_, ha₁'⟩ := hq.obj?_iff.mpr ⟨_, ha₂⟩ 
      have := ha₁.symm.trans ha₁'
      contradiction
    case some.none =>
      have ⟨_, ha₂'⟩ := hq.obj?_iff.mp ⟨_, ha₁⟩ 
      have := ha₂.symm.trans ha₂'
      contradiction
    case some.some a₁ a₂ => 
      refine Finmap.ext _ _ ?_
      intro g
      have ha := he.actions i g.time
      -- this is an exercise in removing alot of unncessecary information 
      -- from the induction, to make its hypothesis usable
      generalize hacs₁ : cs₁.filterMap (·.actionValue? i g.time) = acs₁
      generalize hacs₂ : cs₂.filterMap (·.actionValue? i g.time) = acs₂
      have ⟨a, hc⟩ := h₁.preserves_Equiv.obj?_iff.mpr ⟨_, ha₁⟩
      clear hacs₂
      have hacs₂ := ha.symm.trans hacs₁
      generalize hs' : s = s'
      generalize ha' : a = a'
      have hg : ∀ m, a ⟨g.time, m⟩ = a' ⟨g.time, m⟩ := by simp [ha']
      have hc' := hc
      rw [hs'] at h₂ hc'
      rw [ha'] at hc'
      clear ha' hs' he hq ha
      induction acs₁ generalizing cs₁ cs₂ s s' a a'
      case nil =>
        have hm₁ : ∀ v, .action i g.time v ∉ cs₁ := by
          intro v
          by_contra hc
          have hc' := List.filterMap_nil hacs₁ _ hc
          simp [Change.actionValue?] at hc'
        have hm₂ : ∀ v, .action i g.time v ∉ cs₂ := by
          intro v
          by_contra hc
          have hc' := List.filterMap_nil hacs₂ _ hc
          simp [Change.actionValue?] at hc'
        simp [←h₁.preserves_actions_at_unchanged_times hm₁ hc ha₁ g.microstep,
              ←h₂.preserves_actions_at_unchanged_times hm₂ hc' ha₂ g.microstep]
        exact hg g.microstep
      case cons hd tl hi =>
        have ⟨lhd₁, ltl₁, hl₁, hlhd₁, hltl₁⟩ := List.filterMap_cons hacs₁
        have ⟨lhd₂, ltl₂, hl₂, hlhd₂, hltl₂⟩ := List.filterMap_cons hacs₂
        rw [←hl₁] at h₁
        rw [←hl₂] at h₂
        have ⟨s₁', hshd₁, hstl₁⟩ := h₁.split
        have ⟨s₂', hshd₂, hstl₂⟩ := h₂.split
        have ⟨aq₁, hq₁⟩ := hshd₁.preserves_Equiv.obj?_iff.mp ⟨_, hc⟩
        have ⟨aq₂, hq₂⟩ := hshd₂.preserves_Equiv.obj?_iff.mp ⟨_, hc'⟩
        suffices h : ∀ m, aq₁ ⟨g.time, m⟩ = aq₂ ⟨g.time, m⟩ from hi hstl₁ hltl₁ _ hq₁ hltl₂ _ hstl₂ _ h hq₂
        -- here we build a long chain of equalities of actions at tag g
        --
        -- 1: preparation
        have ⟨l₁, l₂, l₃, h₁, h₁', h₁'', h₁'''⟩ := List.filterMap_singleton_split hlhd₁
        have h₁' := List.filterMap_nil h₁'
        have h₁''' := List.filterMap_nil h₁'''
        rw [←h₁] at hshd₁
        have ⟨_, ho₁⟩ := hshd₁.preserves_Equiv.obj?_iff.mpr ⟨_, hq₁⟩
        have ⟨A2, hshd₁, hshd₁''⟩ := hshd₁.split
        have ⟨A1, hshd₁, hshd₁'⟩ := hshd₁.split
        -- 1: step before hd
        have ⟨_, ho₁'⟩ := hshd₁.preserves_Equiv.obj?_iff.mp ⟨_, ho₁⟩
        have hm₁ : ∀ v, .action i g.time v ∉ l₁ := fun v h => Ne.irrefl $ Change.actionValue?_none (h₁' _ h) v
        have hr₁ := hshd₁.preserves_actions_at_unchanged_times hm₁ ho₁ ho₁'
        -- 1: step hd
        have hshd₁' := ChangeListStep.singleton hshd₁'
        rw [Change.isActionForTime_iff_actionValue?_eq_some.mpr h₁''] at hshd₁'
        cases hshd₁'; case action hu₁ =>
        have ⟨_, hv₁, hv₁'⟩ := hu₁.change'
        -- 1: step after hd
        have ⟨_, ho₁'''⟩ := hshd₁''.preserves_Equiv.obj?_iff.mpr ⟨_, hq₁⟩
        have hm₃ : ∀ v, .action i g.time v ∉ l₃ := fun v h => Ne.irrefl $ Change.actionValue?_none (h₁''' _ h) v
        have hr₃ := hshd₁''.preserves_actions_at_unchanged_times hm₃ ho₁''' hq₁
        -- 2: preparation
        have ⟨l₁', l₂', l₃', h₂, h₂', h₂'', h₂'''⟩ := List.filterMap_singleton_split hlhd₂
        have h₂' := List.filterMap_nil h₂'
        have h₂''' := List.filterMap_nil h₂'''
        rw [←h₂] at hshd₂
        have ⟨_, ho₂⟩ := hshd₂.preserves_Equiv.obj?_iff.mpr ⟨_, hq₂⟩
        have ⟨B2, hshd₂, hshd₂''⟩ := hshd₂.split
        have ⟨B1, hshd₂, hshd₂'⟩ := hshd₂.split 
        -- 2: step before hd
        have ⟨_, ho₂'⟩ := hshd₂.preserves_Equiv.obj?_iff.mp ⟨_, ho₂⟩
        have hm₁' : ∀ v, .action i g.time v ∉ l₁' := fun v h => Ne.irrefl $ Change.actionValue?_none (h₂' _ h) v
        have hr₁' := hshd₂.preserves_actions_at_unchanged_times hm₁' ho₂ ho₂'
        -- 2: step hd
        have hshd₂' := ChangeListStep.singleton hshd₂'
        rw [Change.isActionForTime_iff_actionValue?_eq_some.mpr h₂''] at hshd₂'
        cases hshd₂'; case action hu₂ =>
        have ⟨_, hv₂, hv₂'⟩ := hu₂.change'
        -- 2: step after hd
        have ⟨_, ho₂'''⟩ := hshd₂''.preserves_Equiv.obj?_iff.mpr ⟨_, hq₂⟩
        have hm₃' : ∀ v, .action i g.time v ∉ l₃' := fun v h => Ne.irrefl $ Change.actionValue?_none (h₂''' _ h) v
        have hr₃' := hshd₂''.preserves_actions_at_unchanged_times hm₃' ho₂''' hq₂
        intro m
        simp [ho₁'] at hv₁
        rw [←hv₁] at hv₁'
        simp [hv₁'] at ho₁'''
        rw [←ho₁'''] at hr₃
        rw [←hr₃] 
        simp [ho₂'] at hv₂
        rw [←hv₂] at hv₂'
        simp [hv₂'] at ho₂'''
        rw [←ho₂'''] at hr₃'
        rw [←hr₃' m]
        simp [hc] at ho₁
        simp [hc'] at ho₂
        rw [←ho₁] at hr₁ 
        rw [←ho₂] at hr₁'
        apply schedule_time_inj
        intro m
        simp [←hr₁, ←hr₁', hg]
