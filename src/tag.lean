structure tag := (time_val : ℕ) (microstep_index : ℕ)
variables t₁ t₂ : tag

namespace tag

  protected def lt : Prop := 
  (t₁.time_val < t₂.time_val) ∨ 
  (t₁.time_val = t₂.time_val ∧ t₁.microstep_index < t₂.microstep_index)

  instance : has_lt tag := ⟨tag.lt⟩ 

  protected def plus : tag := 
  ⟨t₁.time_val + t₂.time_val, t₁.microstep_index + t₂.microstep_index⟩

  instance : has_add tag := ⟨tag.plus⟩ 

end tag