import ReactorModel.Determinism.ChangeStep

open Classical

namespace Execution

theorem ChangeListStep.deterministic : (s -[cs]→* s₁) → (s -[cs]→* s₂) → s₁ = s₂ := by
  intro h₁ h₂
  induction h₁ <;> cases h₂ <;> simp_all
  case cons.cons h₁ _ hi h₂ h₂' =>
    simp [h₁.determinisic h₂] at hi
    exact hi h₂'

theorem ChangeListStep.preserves_progress : (s₁ -[cs]→* s₂) → s₁.progress = s₂.progress 
  | .nil .. => rfl
  | .cons h₁₂ h₂₃ => h₁₂.preserves_progress.trans h₂₃.preserves_progress

theorem ChangeListStep.preserves_tag : (s₁ -[cs]→* s₂) → s₁.tag = s₂.tag 
  | .nil .. => rfl
  | .cons h₁₂ h₂₃ => h₁₂.preserves_tag.trans h₂₃.preserves_tag

theorem ChangeListStep.preserves_rcns {i : ID} : (s₁ -[cs]→* s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i)
  | .nil .. => rfl
  | .cons h₁₂ h₂₃ => h₁₂.preserves_rcns.trans h₂₃.preserves_rcns

theorem ChangeListStep.equiv : (s₁ -[cs]→* s₂) → s₁.rtr ≈ s₂.rtr
  | nil .. => .refl
  | cons h hi => h.equiv.trans hi.equiv

theorem ChangeListStep.preserves_unchanged_ports {i : ID} :
  (s₁ -[cs]→* s₂) → (∀ v, .port i v ∉ cs.map (·.obj)) → (s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i)
  | nil ..,    _ => rfl
  | cons h hi, hc => by
    refine (h.preserves_unchanged_port ?_).trans (hi.preserves_unchanged_ports ?_) <;> (
      intro v
      have ⟨_, _⟩ := (not_or ..).mp $ (mt List.mem_cons.mpr) $ hc v
      assumption
    )

theorem ChangeListStep.preserves_unchanged_actions {i : ID} :
  (s₁ -[cs]→* s₂) → (∀ t v, .action i t v ∉ cs.map (·.obj)) → (s₁.rtr.obj? .act i = s₂.rtr.obj? .act i)
  | nil ..,    _ => rfl
  | cons h hi, hc => by
    refine (h.preserves_unchanged_action ?_).trans (hi.preserves_unchanged_actions ?_) <;> (
      intro t v
      have ⟨_, _⟩ := (not_or ..).mp $ (mt List.mem_cons.mpr) $ hc t v
      assumption
    )

theorem ChangeListStep.preserves_unchanged_state {i : ID} :
  (s₁ -[cs]→* s₂) → (∀ v, .state i v ∉ cs.map (·.obj)) → (s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i)
  | nil ..,    _ => rfl
  | cons h hi, hc => by
    refine (h.preserves_unchanged_state ?_).trans (hi.preserves_unchanged_state ?_) <;> (
      intro v
      have ⟨_, _⟩ := (not_or ..).mp $ (mt List.mem_cons.mpr) $ hc v
      assumption
    )

theorem ChangeListStep.preserves_port_role {i : ID} :
  (s₁ -[cs]→* s₂) → (s₁.rtr.obj? .prt i = some p) → (∃ v, s₂.rtr.obj? .prt i = some ⟨v, p.kind⟩)
  | nil ..,     ho => ⟨_, ho⟩
  | cons hd tl, ho => by simp [tl.preserves_port_role (hd.preserves_port_role ho).choose_spec]

theorem ChangeListStep.lastSome?_none_preserves_state_value :
  (s₁ -[cs]→* s₂) → (cs.lastSome? (·.obj.stateValue? i) = none) → (s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i) := by
  intro hs hl 
  have h := (mt List.lastSome?_eq_some_iff.mpr) (Option.eq_none_iff_forall_not_mem.mp hl |> not_exists_of_forall_not)
  exact hs.preserves_unchanged_state (i := i) (by
    intro v hn
    simp at h
    have ⟨c, hm, hn⟩ := List.mem_map.mp hn
    specialize h v ⟨c.id, .state i v⟩
    rw [hn] at h
    specialize h hm
    simp [←hn, Change.stateValue?] at h
  )

theorem ChangeListStep.last_state_value :
  (s₁ -[cs]→* s₂) → (cs.lastSome? (·.obj.stateValue? i) = some v) → (s₂.rtr.obj? .stv i = some v)
  | nil ..,                      hl => by simp [List.lastSome?_empty_eq_none] at hl
  | @cons _ _ _ hd tl hhd htl, hl => by
    by_cases hc : ∃ w, tl.lastSome? (·.obj.stateValue? i) = some w
    case pos =>
      have ⟨w, hc⟩ := hc
      exact htl.last_state_value ((List.lastSome?_tail hl hc).symm ▸ hc)
    case neg =>
      simp at hc
      have hln := Option.eq_none_iff_forall_not_mem.mpr hc
      simp [←htl.lastSome?_none_preserves_state_value hln]
      have hv := List.lastSome?_head hl hln
      cases hhd
      case state hu => 
        have ⟨_, _, h⟩ := hu.change'
        simp at h ⊢
        injection Change.stateValue?_some hv.symm with hi hv
        simp [←hi, ←hv, h]
      all_goals simp [List.lastSome?] at hl; contradiction

theorem ChangeListStep.lastSome?_none_preserves_port_value :
  (s₁ -[cs]→* s₂) → (cs.lastSome? (·.obj.portValue? i) = none) → (s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i) := by
  intro hs hl 
  have h := (mt List.lastSome?_eq_some_iff.mpr) (Option.eq_none_iff_forall_not_mem.mp hl |> not_exists_of_forall_not)
  exact hs.preserves_unchanged_ports (i := i) (by
    intro v hn
    simp at h
    have ⟨c, hm, hn⟩ := List.mem_map.mp hn
    specialize h v ⟨c.id, .port i v⟩ 
    rw [hn] at h
    specialize h hm
    simp [←hn, Change.portValue?] at h
  )

theorem ChangeListStep.last_port_value :
  (s₁ -[cs]→* s₂) → (cs.lastSome? (·.obj.portValue? i) = some v) → (∃ k, s₂.rtr.obj? .prt i = some ⟨v, k⟩)
  | nil ..,                      hl => by simp [List.lastSome?_empty_eq_none] at hl
  | @cons _ _ _ hd tl hhd htl, hl => by
    by_cases hc : ∃ w, tl.lastSome? (·.obj.portValue? i) = some w
    case pos =>
      have ⟨w, hc⟩ := hc
      exact htl.last_port_value ((List.lastSome?_tail hl hc).symm ▸ hc)
    case neg =>
      simp at hc
      have hln := Option.eq_none_iff_forall_not_mem.mpr hc
      simp [←htl.lastSome?_none_preserves_port_value hln]
      have hv := List.lastSome?_head hl hln
      cases hhd
      case port hu => 
        have ⟨_, _, h⟩ := hu.change'
        simp at h ⊢
        injection Change.portValue?_some hv.symm with hi hv
        simp [←hi, ←hv, h]
        sorry
      all_goals simp [List.lastSome?] at hl; contradiction

theorem ChangeListStep.port_change_mem_rtr {i : ID} : 
  (s -[cs]→* s') → (.port i v ∈ cs.map (·.obj)) → (∃ p, s.rtr.obj? .prt i = some p) := by
  intro hs hm
  induction hs
  case nil => contradiction
  case cons hd _ tl hhd htl hi => 
    simp [List.mem_map] at hm
    cases hm
    case inl hp =>
      have hp : hd = ⟨hd.id, .port i v⟩ := by simp [hp] 
      rw [hp] at hhd
      exact hhd.port_change_mem_rtr
    case inr hm =>
      rw [List.mem_map] at hi
      sorry -- exact hhd.preserves_Equiv.obj?_iff.mpr (hi hm)

theorem ChangeListStep.preserves_actions_at_unchanged_times {i : ID} : 
  (s₁ -[cs]→* s₂) → (∀ v, .action i t v ∉ cs.map (·.obj)) → 
  (s₁.rtr.obj? .act i = some a₁) → (s₂.rtr.obj? .act i = some a₂) →
  (∀ m, a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) := by
  intro hs hc ha₁ ha₂ m  
  induction hs generalizing a₁ a₂
  case nil =>
    simp [ha₁] at ha₂
    simp [ha₂]  
  case cons hd _ tl hs₁₂ _ hi =>
    have ⟨_, haₘ⟩ := hs₁₂.equiv.obj?_iff.mp ⟨_, ha₁⟩
    have hhd : ∀ v, .action i t v ≠ hd.obj := by 
      intro v
      exact mt List.mem_cons.mpr (hc v) |> not_or.mp |>.left 
    have htl : ∀ v, .action i t v ∉ tl.map (·.obj) := by 
      intro v
      exact mt List.mem_cons.mpr (hc v) |> not_or.mp |>.right
    simp [hs₁₂.preserves_action_at_unchanged_tags hhd ha₁ haₘ m, hi htl haₘ ha₂]
  
theorem ChangeListStep.context_agnostic :
  (s₁ -[cs]→* s₂) → (s₁.rtr = s₁'.rtr) → (s₁' -[cs]→* { s₂ with tag := s₁'.tag, progress := s₁'.progress }) := by
  intro h hr
  induction h generalizing s₁'
  case nil => simp [ChangeListStep.nil, hr]
  case cons sₘ _ _ _ h₁ _ hi => 
    have h := h₁.context_agnostic hr
    specialize @hi { sₘ with tag := s₁'.tag, progress := s₁'.progress } rfl
    exact ChangeListStep.cons h hi

theorem ChangeListStep.append :
  (s₁ -[cs]→* s₂) → (s₂' -[cs']→* s₃) → (s₂.rtr = s₂'.rtr) → (s₁ -[cs ++ cs']→* { s₃ with tag := s₁.tag, progress := s₁.progress }) := by
  intro h h' hr
  induction h
  case nil => simp [h'.context_agnostic hr.symm]
  case cons h₁ _ hi =>
    specialize hi hr
    rw [←h₁.preserves_tag, ←h₁.preserves_progress] at hi
    exact ChangeListStep.cons h₁ hi

theorem ChangeListStep.split :
  (s₁ -[cs ++ cs']→* s₃) → ∃ s₂, (s₁ -[cs]→* s₂) ∧ (s₂ -[cs']→* s₃) := by
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
  (s₁ -[[c]]→* s₂) → (s₁ -[c]→ s₂) := by
  intro h
  cases h
  case cons h h' =>
    cases h'
    exact h
    
-- NOTE: This was fully proven before updating Lean/Mathlib
theorem ChangeListStep.equiv_changes_eq_result :
  (s -[cs₁]→* s₁) → (s -[cs₂]→* s₂) → (cs₁ ⋈ cs₂) → s₁ = s₂ := by
  intro h₁ h₂ he
  ext1
  case tag => exact h₁.preserves_tag ▸ h₂.preserves_tag
  case progress => exact h₁.preserves_progress ▸ h₂.preserves_progress
  case rtr =>
    have hq := h₁.equiv.symm.trans h₂.equiv
    apply hq.obj?_ext'
    intro cmp i hnr
    cases cmp <;> simp [←h₁.preserves_rcns, ←h₂.preserves_rcns] at hnr ⊢ <;> clear hnr
    case stv =>
      have hs := he.state i
      cases hc : cs₁.lastSome? (·.obj.stateValue? i)
      case none => simp [←h₁.lastSome?_none_preserves_state_value hc, ←h₂.lastSome?_none_preserves_state_value (hs ▸ hc)]
      case some => simp [h₁.last_state_value hc, h₂.last_state_value (hs ▸ hc)]
    case prt =>
      have hp := he.ports i
      cases hc : cs₁.lastSome? (·.obj.portValue? i)
      case none => simp [←h₁.lastSome?_none_preserves_port_value hc, ←h₂.lastSome?_none_preserves_port_value (hp ▸ hc)]
      case some => 
        have ⟨_, hl₁⟩ := h₁.last_port_value hc
        have ⟨_, hl₂⟩ := h₂.last_port_value (hp ▸ hc)
        cases hc' : s.rtr.obj? .prt i
        case none => 
          have ⟨w, c, hm₁, hm₂⟩ := List.lastSome?_eq_some_iff.mp ⟨_, hc⟩
          have ⟨_, hm₃⟩ := h₁.port_change_mem_rtr ((by
            simp [←Change.portValue?_some hm₂, List.mem_map]
            exact ⟨c, hm₁, rfl⟩
          ) : .port i w ∈ cs₁.map (·.obj))
          have := hm₃.symm.trans hc'
          contradiction
        case some =>
          have ⟨_, hr₁⟩ := h₁.preserves_port_role hc'
          have ⟨_, hr₂⟩ := h₂.preserves_port_role hc'
          simp [hl₁, hl₂]
          simp [hr₁] at hl₁
          simp [hr₂] at hl₂
          injection hl₁ with hl₁l hl₁r
          injection hl₂ with hl₂l hl₂r
          rw [hl₁r.symm.trans hl₂r]
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
        refine Finmap.ext ?_
        intro g
        have ha := he.actions i g.time
        -- this is an exercise in removing alot of unncessecary information 
        -- from the induction, to make its hypothesis usable
        generalize hacs₁ : cs₁.filterMap (·.obj.actionValue? i g.time) = acs₁
        generalize hacs₂ : cs₂.filterMap (·.obj.actionValue? i g.time) = acs₂
        have ⟨a, hc⟩ := h₁.equiv.obj?_iff.mpr ⟨_, ha₁⟩
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
          have hm₁ : ∀ v, .action i g.time v ∉ cs₁.map (·.obj) := by
            intro v
            by_contra hc
            have ⟨_, hc, ha⟩ := List.mem_map.mp hc
            have hc' := List.filterMap_nil' hacs₁ _ hc
            simp [←ha, Change.actionValue?] at hc'
          have hm₂ : ∀ v, .action i g.time v ∉ cs₂.map (·.obj) := by
            intro v
            by_contra hc
            have ⟨_, hc, ha⟩ := List.mem_map.mp hc
            have hc' := List.filterMap_nil' hacs₂ _ hc
            simp [←ha, Change.actionValue?] at hc'
          simp [←h₁.preserves_actions_at_unchanged_times hm₁ hc ha₁ g.microstep,
                ←h₂.preserves_actions_at_unchanged_times hm₂ hc' ha₂ g.microstep]
          sorry -- exact hg g.microstep
        case cons hd tl hi =>
          have ⟨lhd₁, ltl₁, hl₁, hlhd₁, hltl₁⟩ := List.filterMap_cons' hacs₁
          have ⟨lhd₂, ltl₂, hl₂, hlhd₂, hltl₂⟩ := List.filterMap_cons' hacs₂
          rw [←hl₁] at h₁
          rw [←hl₂] at h₂
          have ⟨s₁', hshd₁, hstl₁⟩ := h₁.split
          have ⟨s₂', hshd₂, hstl₂⟩ := h₂.split
          have ⟨aq₁, hq₁⟩ := hshd₁.equiv.obj?_iff.mp ⟨_, hc⟩
          have ⟨aq₂, hq₂⟩ := hshd₂.equiv.obj?_iff.mp ⟨_, hc'⟩
          suffices h : ∀ m, aq₁ ⟨g.time, m⟩ = aq₂ ⟨g.time, m⟩ from hi hstl₁ hltl₁ _ hq₁ hltl₂ _ hstl₂ _ h hq₂
          -- here we build a long chain of equalities of actions at tag g
          --
          -- 1: preparation
          have ⟨l₁, l₂, l₃, h₁, h₁', h₁'', h₁'''⟩ := List.filterMap_singleton_split hlhd₁
          have h₁' := List.filterMap_nil' h₁'
          have h₁''' := List.filterMap_nil' h₁'''
          rw [←h₁] at hshd₁
          have ⟨_, ho₁⟩ := hshd₁.equiv.obj?_iff.mpr ⟨_, hq₁⟩
          have ⟨A2, hshd₁, hshd₁''⟩ := hshd₁.split
          have ⟨A1, hshd₁, hshd₁'⟩ := hshd₁.split
          -- 1: step before hd
          have ⟨_, ho₁'⟩ := hshd₁.equiv.obj?_iff.mp ⟨_, ho₁⟩
          have hm₁ : ∀ v, Change.action i g.time v ∉ (l₁.map (·.obj)) := by
            intro v h
            have ⟨_, h, h'⟩ := List.mem_map.mp h
            have h'' := (h₁' _ h)
            rw [←h'] at h''
            exact Ne.irrefl $ Change.actionValue?_none h'' v
          have hr₁ := hshd₁.preserves_actions_at_unchanged_times hm₁ ho₁ ho₁'
          -- 1: step hd
          have hshd₁' := ChangeListStep.singleton hshd₁'
          have hl₂e : l₂ = ⟨l₂.id, .action i g.time hd⟩ := by 
            ext; simp
            simp [Change.isActionForTime_iff_actionValue?_eq_some.mpr h₁'']
          rw [hl₂e] at hshd₁'
          cases hshd₁'; case action hu₁ =>
          have ⟨_, hv₁, hv₁'⟩ := hu₁.change'
          -- 1: step after hd
          have ⟨_, ho₁'''⟩ := hshd₁''.equiv.obj?_iff.mpr ⟨_, hq₁⟩
          have hm₃ : ∀ v, Change.action i g.time v ∉ l₃.map (·.obj) := by
            intro v h
            have ⟨_, h, h'⟩ := List.mem_map.mp h
            have h'' := (h₁''' _ h)
            rw [←h'] at h''
            exact Ne.irrefl $ Change.actionValue?_none h'' v
          have hr₃ := hshd₁''.preserves_actions_at_unchanged_times hm₃ ho₁''' hq₁
          -- 2: preparation
          have ⟨l₁', l₂', l₃', h₂, h₂', h₂'', h₂'''⟩ := List.filterMap_singleton_split hlhd₂
          have h₂' := List.filterMap_nil' h₂'
          have h₂''' := List.filterMap_nil' h₂'''
          rw [←h₂] at hshd₂
          have ⟨_, ho₂⟩ := hshd₂.equiv.obj?_iff.mpr ⟨_, hq₂⟩
          have ⟨B2, hshd₂, hshd₂''⟩ := hshd₂.split
          have ⟨B1, hshd₂, hshd₂'⟩ := hshd₂.split 
          -- 2: step before hd
          have ⟨_, ho₂'⟩ := hshd₂.equiv.obj?_iff.mp ⟨_, ho₂⟩
          have hm₁' : ∀ v, Change.action i g.time v ∉ l₁'.map (·.obj) := by
            intro v h
            have ⟨_, h, h'⟩ := List.mem_map.mp h
            have h'' := (h₂' _ h)
            rw [←h'] at h''
            exact Ne.irrefl $ Change.actionValue?_none h'' v
          have hr₁' := hshd₂.preserves_actions_at_unchanged_times hm₁' ho₂ ho₂'
          -- 2: step hd
          have hshd₂' := ChangeListStep.singleton hshd₂'
          have hl₂e' : l₂' = ⟨l₂'.id, .action i g.time hd⟩ := by 
            ext; simp
            simp [Change.isActionForTime_iff_actionValue?_eq_some.mpr h₂'']
          rw [hl₂e'] at hshd₂'
          cases hshd₂'; case action hu₂ =>
          have ⟨_, hv₂, hv₂'⟩ := hu₂.change'
          -- 2: step after hd
          have ⟨_, ho₂'''⟩ := hshd₂''.equiv.obj?_iff.mpr ⟨_, hq₂⟩
          have hm₃' : ∀ v, Change.action i g.time v ∉ l₃'.map (·.obj) := by
            intro v h
            have ⟨_, h, h'⟩ := List.mem_map.mp h
            have h'' := (h₂''' _ h)
            rw [←h'] at h''
            exact Ne.irrefl $ Change.actionValue?_none h'' v
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
