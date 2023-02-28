import ReactorModel.Determinism.ChangeStep
import ReactorModel.Determinism.ChangeEquiv

open Classical

namespace Execution
namespace ChangeListStep

theorem cons_split : (s₁ -[c :: cs]→* s₃) → ∃ s₂, (s₁ -[c]→ s₂) ∧ (s₂ -[cs]→* s₃)
  | cons e e' => ⟨_, e, e'⟩

theorem append_split (e : s₁ -[cs₁ ++ cs₂]→* s₃) : ∃ s₂, (s₁ -[cs₁]→* s₂) ∧ (s₂ -[cs₂]→* s₃) := by
  induction cs₁ generalizing s₁
  case nil => 
    exists s₁
    simp_all [ChangeListStep.nil]
  case cons hd tl hi =>
    simp [List.cons_append] at e
    have ⟨_, e₁, e₂⟩ := e.cons_split
    have ⟨s₂, e₂, e₃⟩ := hi e₂
    exact ⟨s₂, .cons e₁ e₂, e₃⟩  

theorem lastSome?_some_split (e : s₁ -[cs]→* s₄) (h : cs.lastSome? p = some v) : 
    ∃ cs₁ rcn c cs₂ s₂ s₃, 
    (s₁ -[cs₁]→* s₂) ∧ (s₂ -[⟨rcn, c⟩]→ s₃) ∧ (s₃ -[cs₂]→* s₄) ∧ 
    (p ⟨rcn, c⟩ = some v) ∧ (cs₂.All₂ (p · = none)) ∧ (cs = cs₁ ++ ⟨rcn, c⟩ :: cs₂) := by
  have ⟨cs₁, ⟨rcn, c⟩, cs₂, hcs, hc, hcs₂⟩ := List.lastSome?_eq_some_split h
  subst hcs
  have ⟨s₂, e₁, e₂⟩ := e.append_split
  have ⟨s₃, e₂, e₃⟩ := e₂.cons_split
  exists cs₁, rcn, c, cs₂, s₂, s₃

theorem deterministic : (s -[cs]→* s₁) → (s -[cs]→* s₂) → s₁ = s₂
  | nil, nil => rfl
  | cons e₁ e₁', cons e₂ e₂' => (e₁.deterministic e₂ ▸ e₁').deterministic e₂'

theorem preserves_progress : (s₁ -[cs]→* s₂) → s₁.progress = s₂.progress 
  | nil => rfl
  | cons e e' => e.preserves_progress ▸ e'.preserves_progress

theorem preserves_tag : (s₁ -[cs]→* s₂) → s₁.tag = s₂.tag 
  | nil => rfl
  | cons e e' => e.preserves_tag ▸ e'.preserves_tag

theorem preserves_rcns {i : ID} : (s₁ -[cs]→* s₂) → (s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i)
  | nil => rfl
  | cons e e' => e.preserves_rcns ▸ e'.preserves_rcns

theorem equiv : (s₁ -[cs]→* s₂) → s₁.rtr ≈ s₂.rtr
  | nil .. => .refl
  | cons e e' => e.equiv.trans e'.equiv

theorem preserves_unchanged_ports {i : ID} (h : cs.All₂ (¬·.obj.IsPort i)) : 
    (s₁ -[cs]→* s₂) → s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i
  | nil => rfl
  | cons e e' => by
    have ⟨h, h'⟩ := (List.all₂_cons _ _ _).mp h
    exact e'.preserves_unchanged_ports h' ▸ e.preserves_unchanged_port h

theorem preserves_unchanged_state {i : ID} (h : cs.All₂ (¬·.obj.IsState i)) :
    (s₁ -[cs]→* s₂) → s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i
  | nil => rfl
  | cons e e' => by
    have ⟨h, h'⟩ := (List.all₂_cons _ _ _).mp h
    exact e'.preserves_unchanged_state h' ▸ e.preserves_unchanged_state h

theorem preserves_unchanged_actions {i : ID} (h : cs.All₂ (¬·.obj.IsAction i)) :
    (s₁ -[cs]→* s₂) → (s₁.rtr.obj? .act i = s₂.rtr.obj? .act i)
  | nil => rfl
  | cons e e' => by
    have ⟨h, h'⟩ := (List.all₂_cons _ _ _).mp h
    exact e'.preserves_unchanged_actions h' ▸ e.preserves_unchanged_action h

theorem preserves_port_role {i : ID} (h : s₁.rtr.obj? .prt i = some p): 
    (s₁ -[cs]→* s₂) → ∃ v, s₂.rtr.obj? .prt i = some { p with val := v }
  | nil       => ⟨_, h⟩
  | cons e e' => by simp [e'.preserves_port_role (e.preserves_port_role h).choose_spec]

theorem lastSome?_none_preserves_port_value 
    (e : s₁ -[cs]→* s₂) (h : cs.lastSome? (·.obj.portValue? i) = none) :
    s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i := by
  apply e.preserves_unchanged_ports
  simp [Change.not_IsPort_iff_portValue?_none, List.lastSome?_eq_none h]

theorem lastSome?_none_preserves_state_value 
    (e : s₁ -[cs]→* s₂) (h : cs.lastSome? (·.obj.stateValue? i) = none) :
    s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i := by
  apply e.preserves_unchanged_state
  simp [Change.not_IsState_iff_stateValue?_none, List.lastSome?_eq_none h]

theorem last_state_value (e : s₁ -[cs]→* s₂) (h : cs.lastSome? (·.obj.stateValue? i) = some v) :
    s₂.rtr.obj? .stv i = some v := by
  have ⟨_, _, c, cs, _, _, _, e, e', hc, hcs, _⟩ := e.lastSome?_some_split h
  simp at hc
  rw [Change.stateValue?_some hc] at e
  simp [←Change.not_IsState_iff_stateValue?_none] at hcs
  rw [←e.state_change, ←e'.preserves_unchanged_state hcs]
  
end ChangeListStep




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
    simp [hs₁₂.preserves_action_at_unchanged_times hhd ha₁ haₘ m, hi htl haₘ ha₂]
  
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
