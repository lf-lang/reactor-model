import ReactorModel.Objects
import ReactorModel.Execution.Action

noncomputable section
open ReactorType Updatable Indexable

namespace Reactor

-- TODO: Find a better name for this.
--       * ID rtr cmp
--       * Obj rtr cmp
structure Valid (rtr : Reactor) (cmp : Component) where
  id    : ID
  valid : ∃ obj, rtr[cmp][id] = some obj

namespace Valid

instance {cmp} : Coe (Valid rtr cmp) ID where
  coe := Valid.id

def obj {cmp} (i : Valid rtr cmp) :=
  i.valid.choose

theorem obj?_id_eq_obj {cmp} (i : Valid rtr cmp) : rtr[cmp][i] = i.obj :=
  i.valid.choose_spec

def con {cmp} (i : Valid rtr cmp) : Identified Reactor :=
  obj?_to_con?_and_cmp? i.obj?_id_eq_obj |>.choose

theorem con?_id_eq_con {cmp} (i : Valid rtr cmp) : rtr[cmp][i]& = i.con :=
  obj?_to_con?_and_cmp? i.obj?_id_eq_obj |>.choose_spec.left

end Valid

def apply (rtr : Reactor) : Change → Reactor
  | .prt k i v => update rtr (.prt k) i (fun _ => v)
  | .stv i v   => update rtr .stv     i (fun _ => v)
  | .act i t v => update rtr .act     i (·.schedule t v)
  | .mut ..    => rtr -- Mutations are currently no-ops.

def apply' (rtr : Reactor) (cs : List Change) : Reactor :=
  cs.foldl apply rtr

-- TODO?: Make this handle tag names better.
scoped macro "change_cases " change:term : tactic => 
  `(tactic| cases $change:term <;> try cases ‹Change.Normal›; cases ‹Component.Valued›)

theorem apply_equiv (rtr : Reactor) (c : Change) : rtr.apply c ≈ rtr := by
  change_cases c <;> first | rfl | apply LawfulUpdatable.equiv

theorem apply_preserves_unchanged {cmp} (rtr : Reactor) (c : Change) (h : ¬c.Targets cmp i) :
    (rtr.apply c)[cmp][i] = rtr[cmp][i] := by
  change_cases c <;> first | rfl | exact LawfulUpdatable.obj?_preserved (Change.Targets.norm_not h)

theorem apply_port_change {rtr : Reactor} {i : rtr.Valid $ .prt k} : 
    (rtr.apply $ .prt k i v)[.prt k][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact i.valid

theorem apply_state_change {rtr : Reactor} {i : rtr.Valid $ .stv} : 
    (rtr.apply $ .stv i v)[.stv][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact i.valid

theorem apply_action_change {rtr : Reactor} {i : rtr.Valid $ .act} : 
    (rtr.apply $ .act i t v)[.act][i] = some (i.obj.schedule t v) := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact ⟨_, ⟨i.valid.choose_spec, rfl⟩⟩ 

theorem apply'_equiv (rtr : Reactor) : (cs : List Change) → rtr.apply' cs ≈ rtr 
  | .nil     => .refl
  | .cons hd tl => Equivalent.trans (rtr.apply hd |>.apply'_equiv tl) (apply_equiv rtr hd)

/-
-- Note: `ho₁` and `e` imply that there exists some `a₂` such that `ho₂`.
theorem preserves_same_action_at_unchanged_times
    (e : s₁ -[⟨rcn, .action i t v⟩]→ s₂) (ht : t ≠ t') 
    (ho₁ : s₁.rtr[.act][i] = some a₁) (ho₂ : s₂.rtr[.act][i] = some a₂) :
    a₁ ⟨t', m⟩ = a₂ ⟨t', m⟩ := by
  injection e.action_change ho₁ ▸ ho₂ with h
  rw [←h, schedule_preserves_unchanged_time ht]  

-- Note: `ho₁` and `e` imply that there exists some `a₂` such that `ho₂`.
theorem action_preserves_action_at_unchanged_times
    (e : s₁ -[⟨rcn, .action i t v⟩]→ s₂) (hc : i ≠ j ∨ t ≠ t') 
    (ho₁ : s₁.rtr[.act][j] = some a₁) (ho₂ : s₂.rtr[.act][j] = some a₂) :
    a₁ ⟨t', m⟩ = a₂ ⟨t', m⟩ := by
  by_cases hi : i = j
  case neg =>
    have h := e.preserves_unchanged_action (i := j) (Change.IsActionᵢ.iff_id_eq.not.mpr hi) 
    simp_all [ho₁, ho₂, h]
  case pos =>
    have ht := hc.resolve_left (not_not.mpr hi)
    exact e.preserves_same_action_at_unchanged_times ht (hi ▸ ho₁) (hi ▸ ho₂)

-- Note: `ho₁` and `e` imply that there exists some `a₂` such that `ho₂`.
theorem preserves_action_at_unchanged_times
    (e : s₁ -[⟨rcn, c⟩]→ s₂) (hc : ¬c.IsActionₜ i t) 
    (ho₁ : s₁.rtr[.act][i] = some a₁) (ho₂ : s₂.rtr[.act][i] = some a₂) :
    a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩ := by
  cases c <;> try cases ‹Change.Normal›   
  case norm.action j t v =>
    have ht := Change.IsActionₜ.not_to_ne_ids_or_ne_time hc
    exact e.action_preserves_action_at_unchanged_times ht ho₁ ho₂
  all_goals
    injection ho₁ ▸ ho₂ ▸ e.preserves_unchanged_action with h
    simp [h]

-- This theorem upgrades `preserves_action_at_unchanged_times`.
theorem preserves_action_at_unchanged_times'
    (e : s₁ -[⟨rcn, c⟩]→ s₂) (hc : ¬c.IsActionₜ i t) (ho₁ : s₁.rtr[.act][i] = some a₁) :
    ∃ a₂, (s₂.rtr[.act][i] = some a₂) ∧ (a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) := by
  have ⟨a₂, ho₂⟩ := e.equiv.obj?_some_iff.mp ⟨_, ho₁⟩ 
  exists a₂, ho₂
  exact e.preserves_action_at_unchanged_times hc ho₁ ho₂

-/

/-
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

theorem preserves_progress : (s₁ -[cs]→* s₂) → s₁.progress = s₂.progress 
  | nil => rfl
  | cons e e' => e.preserves_progress ▸ e'.preserves_progress

theorem preserves_tag : (s₁ -[cs]→* s₂) → s₁.tag = s₂.tag 
  | nil => rfl
  | cons e e' => e.preserves_tag ▸ e'.preserves_tag

theorem preserves_rcns : (s₁ -[cs]→* s₂) → s₁.rtr[.rcn] = s₂.rtr[.rcn]
  | nil => rfl
  | cons e e' => e.preserves_rcns ▸ e'.preserves_rcns

open ReactorType in
theorem equiv : (s₁ -[cs]→* s₂) → s₁.rtr ≈ s₂.rtr
  | nil .. => Equivalent.refl
  | cons e e' => Equivalent.trans e.equiv e'.equiv

theorem preserves_unchanged_ports {i : ID} (h : cs.All₂ (¬·.obj.IsPortᵢ k i)) : 
    (s₁ -[cs]→* s₂) → s₁.rtr[.prt k][i] = s₂.rtr[.prt k][i]
  | nil => rfl
  | cons e e' => by
    have ⟨h, h'⟩ := (List.all₂_cons _ _ _).mp h
    exact e'.preserves_unchanged_ports h' ▸ e.preserves_unchanged_port h

theorem preserves_unchanged_state {i : ID} (h : cs.All₂ (¬·.obj.IsStateᵢ i)) :
    (s₁ -[cs]→* s₂) → s₁.rtr[.stv][i] = s₂.rtr[.stv][i]
  | nil => rfl
  | cons e e' => by
    have ⟨h, h'⟩ := (List.all₂_cons _ _ _).mp h
    exact e'.preserves_unchanged_state h' ▸ e.preserves_unchanged_state h

theorem preserves_unchanged_actions {i : ID} (h : cs.All₂ (¬·.obj.IsActionᵢ i)) :
    (s₁ -[cs]→* s₂) → s₁.rtr[.act][i] = s₂.rtr[.act][i]
  | nil => rfl
  | cons e e' => by
    have ⟨h, h'⟩ := (List.all₂_cons _ _ _).mp h
    exact e'.preserves_unchanged_actions h' ▸ e.preserves_unchanged_action h

theorem preserves_actions_at_unchanged_times {i : ID} 
    (e : s₁ -[cs]→* s₂) (h : cs.All₂ (¬·.obj.IsActionₜ i t)) (ho₁ : s₁.rtr[.act][i] = some a₁) :
    ∃ a₂, (s₂.rtr[.act][i] = some a₂) ∧ (a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) := by
  induction e generalizing a₁
  case nil => exists a₁
  case cons e _ hi =>
    have ⟨h, h'⟩ := (List.all₂_cons _ _ _).mp h
    have ⟨a, ho, ha⟩ := e.preserves_action_at_unchanged_times' h ho₁ (m := m)
    simp [ha, hi h' ho]

end ChangeListStep
-/

end Reactor