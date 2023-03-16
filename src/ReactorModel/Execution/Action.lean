import ReactorModel.Primitives

namespace Action

def schedule (a : Action) (t : Time) (v : Value) : Action :=
  match a.tags.filter (·.time = t) |>.max with
  | ⊥           => a.insert ⟨t, 0⟩ v
  | some ⟨_, m⟩ => a.insert ⟨t, m + 1⟩ v

theorem schedule_preserves_unchanged_time (h : t ≠ t') : a ⟨t', m⟩ = schedule a t v ⟨t', m⟩ := by
  sorry

def schedule' (a : Action) (t : Time) (vs : List Value) : Action :=
  vs.foldl (schedule · t ·) a

theorem schedule'_cons (a : Action) : schedule' a t (hd :: tl) = schedule' (schedule a t hd) t tl := 
  rfl

theorem schedule'_tag_congr {a₁ a₂ : Action} 
    (h : a₁ ⟨t, m⟩ = a₂ ⟨t, m⟩) : schedule' a₁ t l ⟨t, m⟩ = schedule' a₂ t l ⟨t, m⟩ :=
  sorry

end Action