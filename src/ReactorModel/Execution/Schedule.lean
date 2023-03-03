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

theorem schedule_preserves_unchanged_time (h : t ≠ t') : a ⟨t', m⟩ = schedule a t v ⟨t', m⟩ := by
  sorry

noncomputable def schedule' (act : Time.Tag ⇉ Value) (t : Time) : (List Value) → Time.Tag ⇉ Value
  | .nil => act
  | .cons v tl => schedule' (schedule act t v) t tl

theorem schedule'_cons (act : Time.Tag ⇉ Value) : 
    schedule' act t (hd :: tl) = schedule' (schedule act t hd) t tl := 
  rfl

theorem schedule'_tag_congr {act₁ act₂ : Time.Tag ⇉ Value} (h : act₁ ⟨t, m⟩ = act₂ ⟨t, m⟩) :
    (schedule' act₁ t l) ⟨t, m⟩ = (schedule' act₂ t l) ⟨t, m⟩ :=
  sorry

end Execution