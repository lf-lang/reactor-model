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

-- TODO: If this isn't used in `InstStep/InstExecution.lean` reduce the resulting facts, to only 
--       those which are actually used by theorems using this theorem.
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

theorem preserves_port_kind {i : ID} (h : s₁.rtr.obj? .prt i = some p) : 
    (s₁ -[cs]→* s₂) → ∃ v, s₂.rtr.obj? .prt i = some { p with val := v }
  | nil       => ⟨_, h⟩
  | cons e e' => by simp [e'.preserves_port_kind (e.preserves_port_kind h).choose_spec]

theorem port_kind_deterministic {i : ID} 
    (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂)
    (ho₁ : s₁.rtr.obj? .prt i = some { kind := k₁, val := v₁ }) 
    (ho₂ : s₂.rtr.obj? .prt i = some { kind := k₂, val := v₂ }) : 
    k₁ = k₂ := by
  have ⟨_, h₁⟩ := e₁.equiv.obj?_iff.mpr ⟨_, ho₁⟩ 
  have ⟨_, h₂⟩ := e₂.equiv.obj?_iff.mpr ⟨_, ho₂⟩ 
  injection h₁ ▸ h₂ with h
  subst h
  have ⟨_, h₁⟩ := e₁.preserves_port_kind h₁
  have ⟨_, h₂⟩ := e₂.preserves_port_kind h₂
  injection h₁ ▸ ho₁ with h₁
  injection h₂ ▸ ho₂ with h₂
  injection h₁
  injection h₂
  simp_all

theorem lastSome?_none_preserves_ports 
    (e : s₁ -[cs]→* s₂) (h : cs.lastSome? (·.obj.portValue? i) = none) :
    s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i := by
  apply e.preserves_unchanged_ports
  simp [Change.not_IsPort_iff_portValue?_none, List.lastSome?_eq_none h]

theorem lastSome?_some_port 
    (e : s₁ -[cs]→* s₂) (h : cs.lastSome? (·.obj.portValue? i) = some v) :
    ∃ k, s₂.rtr.obj? .prt i = some { val := v, kind := k } := by
  have ⟨_, _, c, cs, _, _, _, e, e', hc, hcs, _⟩ := e.lastSome?_some_split h
  simp at hc
  rw [Change.portValue?_some hc] at e
  simp [←Change.not_IsPort_iff_portValue?_none] at hcs
  rw [←e'.preserves_unchanged_ports hcs]
  have ⟨k, _⟩ := e.port_change
  exists k
  
theorem lastSome?_none_preserves_state 
    (e : s₁ -[cs]→* s₂) (h : cs.lastSome? (·.obj.stateValue? i) = none) :
    s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i := by
  apply e.preserves_unchanged_state
  simp [Change.not_IsState_iff_stateValue?_none, List.lastSome?_eq_none h]

theorem lastSome?_some_state (e : s₁ -[cs]→* s₂) (h : cs.lastSome? (·.obj.stateValue? i) = some v) :
    s₂.rtr.obj? .stv i = some v := by
  have ⟨_, _, c, cs, _, _, _, e, e', hc, hcs, _⟩ := e.lastSome?_some_split h
  simp at hc
  rw [Change.stateValue?_some hc] at e
  simp [←Change.not_IsState_iff_stateValue?_none] at hcs
  rw [←e'.preserves_unchanged_state hcs, ←e.state_change]
  
theorem preserves_actions_at_unchanged_times {i : ID} 
    (e : s₁ -[cs]→* s₂) (h : cs.All₂ (¬·.obj.IsActionAt i t)) (ho₁ : s₁.rtr.obj? .act i = some a₁) :
    ∃ a₂, (s₂.rtr.obj? .act i = some a₂) ∧ (a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) := by
  induction e generalizing a₁
  case nil => exists a₁
  case cons e _ hi =>
    have ⟨h, h'⟩ := (List.all₂_cons _ _ _).mp h
    have ⟨a, ho, ha⟩ := e.preserves_action_at_unchanged_times' h ho₁ (m := m)
    simp [ha, hi h' ho]

theorem equiv_changes_eq_ports {i : ID} (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : cs₁ ⋈ cs₂) : 
    s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i :=
  have hl := h.ports i
  match hc : cs₁.lastSome? (·.obj.portValue? i) with
  | none    => e₁.lastSome?_none_preserves_ports hc ▸ e₂.lastSome?_none_preserves_ports (hl ▸ hc)
  | some .. => by 
    have ⟨_, h₁⟩ := e₁.lastSome?_some_port hc
    have ⟨_, h₂⟩ := e₂.lastSome?_some_port (hl ▸ hc)
    simp [h₁, h₂, e₁.port_kind_deterministic e₂ h₁ h₂]

theorem equiv_changes_eq_state {i : ID} (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : cs₁ ⋈ cs₂) : 
    s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i :=
  have hl := h.state i
  match hc : cs₁.lastSome? (·.obj.stateValue? i) with
  | none    => e₁.lastSome?_none_preserves_state hc ▸ e₂.lastSome?_none_preserves_state (hl ▸ hc)
  | some .. => by simp [e₁.lastSome?_some_state hc, e₂.lastSome?_some_state (hl ▸ hc)]

theorem equiv_changes_eq_actions {i : ID} 
    (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : cs₁ ⋈ cs₂) : 
    s₁.rtr.obj? .act i = s₂.rtr.obj? .act i := by
  sorry

theorem equiv_changes_eq_rtr (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : cs₁ ⋈ cs₂) : 
    s₁.rtr = s₂.rtr := by
  apply (e₁.equiv.symm.trans e₂.equiv).obj?_ext'
  intro cmp _ _
  cases cmp
  case prt => exact e₁.equiv_changes_eq_ports e₂ h
  case stv => exact e₁.equiv_changes_eq_state e₂ h
  case act => exact e₁.equiv_changes_eq_actions e₂ h
  case rcn => exact e₁.preserves_rcns ▸ e₂.preserves_rcns
  case rtr => contradiction

theorem equiv_changes_deterministic (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : cs₁ ⋈ cs₂) : 
    s₁ = s₂ := by
  ext1
  case tag      => exact e₁.preserves_tag ▸ e₂.preserves_tag
  case progress => exact e₁.preserves_progress ▸ e₂.preserves_progress
  case rtr      => exact e₁.equiv_changes_eq_rtr e₂ h

end ChangeListStep




-- TODO: Check if this is still needed after cleaning up `ChangeListStep.equiv_changes_eq_result`.
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
  case tag => sorry
  case progress => sorry
  case rtr =>
    have hq := h₁.equiv.symm.trans h₂.equiv
    apply hq.obj?_ext'
    intro cmp i hnr
    cases cmp
    case act =>
      clear hnr
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
          have ⟨s₁', hshd₁, hstl₁⟩ := h₁.append_split
          have ⟨s₂', hshd₂, hstl₂⟩ := h₂.append_split
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
          have ⟨A2, hshd₁, hshd₁''⟩ := hshd₁.append_split
          have ⟨A1, hshd₁, hshd₁'⟩ := hshd₁.append_split
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
    all_goals sorry




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

