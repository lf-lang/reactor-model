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

-- TODO: If this isn't used in `InstStep/InstExecution.lean`, reduce the resulting facts to only 
--       those which are actually used by theorems using this theorem.
theorem lastSome?_some_split (e : s₁ -[cs]→* s₄) (h : cs.lastSome? f = some v) : 
    ∃ cs₁ rcn c cs₂ s₂ s₃, 
    (s₁ -[cs₁]→* s₂) ∧ (s₂ -[⟨rcn, c⟩]→ s₃) ∧ (s₃ -[cs₂]→* s₄) ∧ 
    (f ⟨rcn, c⟩ = some v) ∧ (cs₂.All₂ (f · = none)) ∧ (cs = cs₁ ++ ⟨rcn, c⟩ :: cs₂) := by
  have ⟨cs₁, ⟨rcn, c⟩, cs₂, hcs, hc, hcs₂⟩ := List.lastSome?_eq_some_split h
  subst hcs
  have ⟨s₂, e₁, e₂⟩ := e.append_split
  have ⟨s₃, e₂, e₃⟩ := e₂.cons_split
  exists cs₁, rcn, c, cs₂, s₂, s₃

-- TODO: If this isn't used in `InstStep/InstExecution.lean`, reduce the resulting facts to only 
--       those which are actually used by theorems using this theorem.
theorem filterMap_cons_split (e : s₁ -[cs]→* s₄) (h : cs.filterMap f = hd :: tl) : 
    ∃ cs₁ rcn c cs₂ s₂ s₃, 
    (s₁ -[cs₁]→* s₂) ∧ (s₂ -[⟨rcn, c⟩]→ s₃) ∧ (s₃ -[cs₂]→* s₄) ∧ (cs₁.All₂ (f · = none)) ∧ 
    (f ⟨rcn, c⟩ = some hd) ∧ (cs₂.filterMap f = tl) ∧ (cs = cs₁ ++ ⟨rcn, c⟩ :: cs₂) := by
  have ⟨cs₁, ⟨rcn, c⟩, cs₂, hcs, hcs₁, hc, hcs₂⟩ := List.filterMap_cons_split h
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

theorem filterMap_nil_preserves_actions_at_time {i : ID}
    (e : s₁ -[cs]→* s₂) (h : cs.filterMap (·.obj.actionValue? i t) = []) 
    (ho₁ : s₁.rtr.obj? .act i = some a₁) (ho₂ : s₂.rtr.obj? .act i = some a₂) : 
    a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩ := by
  have h := List.filterMap_nil_iff.mp h
  simp [←Change.not_IsActionAt_iff_actionValue?_none] at h
  have ⟨_, h, ht⟩ := e.preserves_actions_at_unchanged_times h ho₁ (t := t) (m := m)
  simp_all

theorem action_at_time_eq_schedule'_filterMap {i : ID} 
    (e : s₁ -[cs]→* s₂) (ho₁ : s₁.rtr.obj? .act i = some a₁) (ho₂ : s₂.rtr.obj? .act i = some a₂) :
    a₂ ⟨t, m⟩ = (schedule' a₁ t $ cs.filterMap (·.obj.actionValue? i t)) ⟨t, m⟩ := by
  generalize hl : cs.filterMap (·.obj.actionValue? i t) = l
  induction l generalizing a₁ a₂ s₁ s₂ cs
  case nil => simp [schedule', e.filterMap_nil_preserves_actions_at_time hl ho₁ ho₂]
  case cons hd tl hi =>
    have ⟨_, _, _, _, _, _, e₁, e₂, e₃, hcs₁, hc, hcs₂, _⟩ := e.filterMap_cons_split hl
    cases Change.actionValue?_some hc
    simp [←Change.not_IsActionAt_iff_actionValue?_none] at hcs₁
    have ⟨_, ho, h⟩ := e₁.preserves_actions_at_unchanged_times hcs₁ ho₁ (t := t) (m := m)
    simp [hi e₃ (e₂.action_change ho) ho₂ hcs₂, ←schedule'_cons, schedule'_tag_congr h]

theorem equiv_changes_eq_ports {i : ID} 
    (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : PortChangeEquiv cs₁ cs₂) : 
    s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i :=
  match hc : cs₁.lastSome? (·.obj.portValue? i) with
  | none   => e₁.lastSome?_none_preserves_ports hc ▸ e₂.lastSome?_none_preserves_ports (h i ▸ hc)
  | some _ => by 
    have ⟨_, h₁⟩ := e₁.lastSome?_some_port hc
    have ⟨_, h₂⟩ := e₂.lastSome?_some_port (h i ▸ hc)
    simp [h₁, h₂, e₁.port_kind_deterministic e₂ h₁ h₂]

theorem equiv_changes_eq_state {i : ID} 
    (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : StateChangeEquiv cs₁ cs₂) : 
    s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i :=
  match hc : cs₁.lastSome? (·.obj.stateValue? i) with
  | none   => e₁.lastSome?_none_preserves_state hc ▸ e₂.lastSome?_none_preserves_state (h i ▸ hc)
  | some _ => by simp [e₁.lastSome?_some_state hc, e₂.lastSome?_some_state (h i ▸ hc)]

theorem equiv_changes_eq_present_actions {i : ID} 
    (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : ActionChangeEquiv cs₁ cs₂) 
    (ho₁ : s₁.rtr.obj? .act i = some a₁) (ho₂ : s₂.rtr.obj? .act i = some a₂) :
    a₁ = a₂ := by
  refine Finmap.ext ?_
  intro ⟨t, m⟩ 
  have ⟨_, ho⟩ := e₁.equiv.obj?_iff.mpr ⟨_, ho₁⟩
  simp [
    e₁.action_at_time_eq_schedule'_filterMap ho ho₁,
    e₂.action_at_time_eq_schedule'_filterMap ho ho₂,
    h i t
  ]

theorem equiv_changes_eq_actions {i : ID} 
    (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : ActionChangeEquiv cs₁ cs₂) : 
    s₁.rtr.obj? .act i = s₂.rtr.obj? .act i :=
  match ha : s.rtr.obj? .act i with
  | none => (e₂.equiv.obj?_none_iff.mp ha) ▸ (e₁.equiv.obj?_none_iff.mp ha)
  | some _ => 
    have ⟨_, h₁⟩ := e₁.equiv.obj?_iff.mp ⟨_, ha⟩
    have ⟨_, h₂⟩ := e₂.equiv.obj?_iff.mp ⟨_, ha⟩
    e₁.equiv_changes_eq_present_actions e₂ h h₁ h₂ ▸ h₁ |>.trans h₂.symm

theorem equiv_changes_eq_rtr (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : cs₁ ⋈ cs₂) : 
    s₁.rtr = s₂.rtr := by
  apply (e₁.equiv.symm.trans e₂.equiv).obj?_ext'
  intro cmp _ _
  cases cmp
  case prt => exact e₁.equiv_changes_eq_ports e₂ h.ports
  case stv => exact e₁.equiv_changes_eq_state e₂ h.state
  case act => exact e₁.equiv_changes_eq_actions e₂ h.actions
  case rcn => exact e₁.preserves_rcns ▸ e₂.preserves_rcns
  case rtr => contradiction

theorem equiv_changes_deterministic (e₁ : s -[cs₁]→* s₁) (e₂ : s -[cs₂]→* s₂) (h : cs₁ ⋈ cs₂) : 
    s₁ = s₂ := by
  ext1
  case tag      => exact e₁.preserves_tag ▸ e₂.preserves_tag
  case progress => exact e₁.preserves_progress ▸ e₂.preserves_progress
  case rtr      => exact e₁.equiv_changes_eq_rtr e₂ h

end ChangeListStep






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

