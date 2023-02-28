import ReactorModel.Primitives

namespace Execution

-- NOTE: This does not constrain actions to have to be scheduled into the future.
--       If we schedule something for the past, it doesn't matter, since that action value will never be read.
--       But if the current tag has a microstep of 0, it is possible to schedule something for the current tag
--       (in the `none` case).
noncomputable def schedule (act : Time.Tag ⇉ Value) (t : Time) (v : Value) : Time.Tag ⇉ Value :=
  match act.ids.filter (·.time = t) |>.max with
  | none => act.update ⟨t, 0⟩ v
  | some g => act.update ⟨t, g.microstep + 1⟩ v

theorem schedule_preserves_unchanged_time (h : t ≠ t') : a ⟨t', m⟩ = (schedule a t v) ⟨t', m⟩ := by
  unfold schedule
  split
  all_goals
    apply Eq.symm
    sorry
    -- apply Finmap.update_ne
    -- simp [h]

theorem schedule_time_inj :
  (∀ m, a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) → (schedule a₁ t v) ⟨t, m⟩ = (schedule a₂ t v) ⟨t, m⟩ := by
  intro h
  unfold schedule
  cases a₁.ids.filter (·.time = t) |>.max <;>
  cases a₂.ids.filter (·.time = t) |>.max
  case' none.none, none.some =>
    cases m
    case zero => sorry -- simp [Finmap.update_self]
    case succ => sorry -- simp [Finmap.update_ne, h]
  case' some.some m₁ _, some.none m₁ =>
    simp
    by_cases hm : m₁.microstep + 1 = m
    case pos => sorry -- simp [hm, Finmap.update_self]
    case neg => 
      sorry
      -- have hm' : Time.Tag.mk t (m₁.microstep + 1) ≠ ⟨t, m⟩ := by simp [hm]
      -- simp [Finmap.update_ne _ hm', h
  
end Execution