import ReactorModel.Execution

open Classical

namespace Execution
namespace ChangeStep

theorem preserves_progress (e : s₁ -[c]→ s₂) : s₁.progress = s₂.progress := by
  cases e <;> rfl

theorem preserves_tag (e : s₁ -[c]→ s₂) : s₁.tag = s₂.tag := by
  cases e <;> rfl

theorem preserves_rcns {i : ID} (e : s₁ -[c]→ s₂) : s₁.rtr.obj? .rcn i = s₂.rtr.obj? .rcn i := by
  cases e <;> first | rfl | simp [Reactor.Update.preserves_ne_cmp_or_id ‹_›]

theorem equiv (e : s₁ -[c]→ s₂) : s₁.rtr ≈ s₂.rtr := by
  cases e 
  case' port h, state h, action h => exact h.equiv
  all_goals exact .refl 

theorem preserves_unchanged_port (e : s₁ -[c]→ s₂) (h : ¬c.obj.IsPort i := by exact (nomatch ·)) :
    s₁.rtr.obj? .prt i = s₂.rtr.obj? .prt i := by
  cases e
  case port u => simp [Change.IsPort.iff_id_eq] at h; exact u.preserves_ne_id h
  case' state u, action u => exact u.preserves_ne_cmp
  all_goals rfl

theorem preserves_unchanged_state (e : s₁ -[c]→ s₂) (h : ¬c.obj.IsState i := by exact (nomatch ·)) : 
    s₁.rtr.obj? .stv i = s₂.rtr.obj? .stv i := by
  cases e
  case state u => simp [Change.IsState.iff_id_eq] at h; exact u.preserves_ne_id h
  case' action u, port u => exact u.preserves_ne_cmp
  all_goals rfl

theorem preserves_unchanged_action 
    (e : s₁ -[c]→ s₂) (h : ¬c.obj.IsAction i := by exact (nomatch ·)) : 
    s₁.rtr.obj? .act i = s₂.rtr.obj? .act i := by
  cases e 
  case action u => simp [Change.IsAction.iff_id_eq] at h; exact u.preserves_ne_id h
  case' state u, port u => exact u.preserves_ne_cmp 
  all_goals rfl

-- TODO: It might be simpler here to add the condition that `s₁.rtr.obj? .prt i = some p` and then
--       include the port kind in the result. Then we don't have to prove things about the ports
--       value and kind separately. Cf. `ChangeListStep.lastSome?_some_port` for details on how
--       this split complicates things.
--       How is this related to `port_change'`?
theorem port_change : 
    (s₁ -[⟨rcn, .port i v⟩]→ s₂) → ∃ k, s₂.rtr.obj? .prt i = some { val := v, kind := k }
  | port u => by
    have ⟨p, _, _⟩ := u.change'
    exists p.kind    

theorem state_change : (s₁ -[⟨rcn, .state i v⟩]→ s₂) → s₂.rtr.obj? .stv i = some v
  | state u => u.change'.choose_spec.right

theorem action_change {i : ID} (h : s₁.rtr.obj? .act i = some a) :
    (s₁ -[⟨rcn, .action i t v⟩]→ s₂) → s₂.rtr.obj? .act i = some (schedule a t v)
  | action u => by
    have ⟨_, h₁, h₂⟩ := u.change'
    simp_all [h, h₁, h₂]

theorem port_change' {i : ID} (h : s₁.rtr.obj? .prt i = some p) :
    (s₁ -[⟨rcn, .port i v⟩]→ s₂) → s₂.rtr.obj? .prt i = some { p with val := v }
  | port u => by
    have ⟨_, h₁, h₂⟩ := u.change'
    simp_all [h, h₁, h₂]

theorem port_preserves_port_kind {j : ID} 
    (e : s₁ -[⟨rcn, .port i v⟩]→ s₂) (h : s₁.rtr.obj? .prt j = some p) :
    ∃ v, s₂.rtr.obj? .prt j = some { p with val := v } :=
  if hi : i = j
  then ⟨v, hi ▸ e.port_change' (hi ▸ h)⟩ 
  else ⟨_, e.preserves_unchanged_port (Change.IsPort.iff_id_eq.not.mpr hi) ▸ h⟩ 

theorem preserves_port_kind {i : ID} (e : s₁ -[⟨rcn, c⟩]→ s₂) (h : s₁.rtr.obj? .prt i = some p) :
    ∃ v, s₂.rtr.obj? .prt i = some { p with val := v } := by
  cases c
  case port => exact e.port_preserves_port_kind h
  all_goals
    simp [←e.preserves_unchanged_port (i := i), h]
    exists p.val

-- Note: `ho₁` and `e` imply that there exists some `a₂` such that `ho₂`.
theorem preserves_same_action_at_unchanged_times
    (e : s₁ -[⟨rcn, .action i t v⟩]→ s₂) (ht : t ≠ t') 
    (ho₁ : s₁.rtr.obj? .act i = some a₁) (ho₂ : s₂.rtr.obj? .act i = some a₂) :
    a₁ ⟨t', m⟩ = a₂ ⟨t', m⟩ := by
  injection e.action_change ho₁ ▸ ho₂ with h
  rw [←h, schedule_preserves_unchanged_time ht]  

-- Note: `ho₁` and `e` imply that there exists some `a₂` such that `ho₂`.
theorem action_preserves_action_at_unchanged_times
    (e : s₁ -[⟨rcn, .action i t v⟩]→ s₂) (hc : i ≠ j ∨ t ≠ t') 
    (ho₁ : s₁.rtr.obj? .act j = some a₁) (ho₂ : s₂.rtr.obj? .act j = some a₂) :
    a₁ ⟨t', m⟩ = a₂ ⟨t', m⟩ := by
  by_cases hi : i = j
  case neg =>
    have h := e.preserves_unchanged_action (i := j) (Change.IsAction.iff_id_eq.not.mpr hi) 
    simp_all [ho₁, ho₂, h]
  case pos =>
    have ht := hc.resolve_left (not_not.mpr hi)
    exact e.preserves_same_action_at_unchanged_times ht (hi ▸ ho₁) (hi ▸ ho₂)

-- Note: `ho₁` and `e` imply that there exists some `a₂` such that `ho₂`.
theorem preserves_action_at_unchanged_times
    (e : s₁ -[⟨rcn, c⟩]→ s₂) (hc : ¬c.IsActionAt i t) 
    (ho₁ : s₁.rtr.obj? .act i = some a₁) (ho₂ : s₂.rtr.obj? .act i = some a₂) :
    a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩ := by
  cases c
  case action j t v =>
    have ht := Change.not_IsActionAt_ne_ids_or_ne_time hc
    exact e.action_preserves_action_at_unchanged_times ht ho₁ ho₂
  all_goals
    injection ho₁ ▸ ho₂ ▸ e.preserves_unchanged_action with h
    simp [h]

-- This theorem upgrades `preserves_action_at_unchanged_times`.
theorem preserves_action_at_unchanged_times'
    (e : s₁ -[⟨rcn, c⟩]→ s₂) (hc : ¬c.IsActionAt i t) (ho₁ : s₁.rtr.obj? .act i = some a₁) :
    ∃ a₂, (s₂.rtr.obj? .act i = some a₂) ∧ (a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) := by
  have ⟨a₂, ho₂⟩ := e.equiv.obj?_iff.mp ⟨_, ho₁⟩ 
  exists a₂, ho₂
  exact e.preserves_action_at_unchanged_times hc ho₁ ho₂

theorem context_agnostic (e : s₁ -[c]→ s) (h : s₁.rtr = s₂.rtr) :
    s₂ -[c]→ { s with tag := s₂.tag, progress := s₂.progress } := by
  cases e
  all_goals 
    rw [h] at * 
    constructor <;> assumption

theorem deterministic (e₁ : s -[c]→ s₁) (e₂ : s -[c]→ s₂) : s₁ = s₂ := by
  cases e₁ <;> cases e₂ <;> simp <;> try apply Reactor.Update.unique' ‹_› ‹_› 

end ChangeStep
end Execution