import ReactorModel.Objects.Reactor.ReactorType.Indexable

namespace ReactorType

-- TODO: Adding equality of reactions makes Equivalent Dependency-graph preserving.
def Equivalent [Indexable α] (rtr₁ rtr₂ : α) : Prop := 
  ∀ cmp, rtr₁[cmp]&.map (·.id) = rtr₂[cmp]&.map (·.id)

namespace Equivalent

variable [Indexable α]

instance : HasEquiv α where 
  Equiv := Equivalent

@[refl]
protected theorem refl {rtr : α} : rtr ≈ rtr :=
  fun _ => rfl

@[symm]
protected theorem symm {rtr₁ : α} (e : rtr₁ ≈ rtr₂) : rtr₂ ≈ rtr₁ :=
  fun cmp => e cmp |>.symm

@[trans]
protected theorem trans {rtr₁ : α} (e₁ : rtr₁ ≈ rtr₂) (e₂ : rtr₂ ≈ rtr₃) : rtr₁ ≈ rtr₃ := 
  fun cmp => e₁ cmp |>.trans (e₂ cmp)

theorem obj?_some_iff {rtr₁ : α} {cmp} {i : ID} (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, rtr₁[cmp][i] = some o₁) ↔ (∃ o₂, rtr₂[cmp][i] = some o₂) := 
  sorry

theorem obj?_none_iff {rtr₁ : α} {cmp} {i : ID} (e : rtr₁ ≈ rtr₂) : 
    (rtr₁[cmp][i] = none) ↔ (rtr₂[cmp][i] = none) := by 
  sorry

/-
theorem obj?_eq_to_cmp?_eq {rtr₁ : α} {cmp} (e : rtr₁ ≈ rtr₂) (h : rtr₁[cmp] = rtr₂[cmp]) : 
    cmp? cmp rtr₁ = cmp? cmp rtr₂ := by
  sorry

theorem cmp?_eq_empty {rtr₁ : α} {cmp} (e : rtr₁ ≈ rtr₂) (h : cmp? cmp rtr₁ = ∅) : 
    cmp? cmp rtr₂ = ∅ := by
  sorry

theorem weak_ext_obj? {rtr₁ : α} (e : rtr₁ ≈ rtr₂) (h : ∀ cmp, rtr₁[cmp] = rtr₂[cmp]) : 
    rtr₁ = rtr₂ := by
  ext
  split_ands
  · funext k; exact obj?_eq_to_cmp?_eq e (h $ .prt k)
  · exact obj?_eq_to_cmp?_eq e (h .act)
  · exact obj?_eq_to_cmp?_eq e (h .stv)
  · exact obj?_eq_to_cmp?_eq e (h .rcn)
  · exact obj?_eq_to_cmp?_eq e (h .rtr)
-/

-- TODO?: Find an `obj?`-based induction principle.
theorem ext_obj? {rtr₁ : α} (e : rtr₁ ≈ rtr₂) (h : ∀ cmp, (cmp ≠ .rtr) → rtr₁[cmp] = rtr₂[cmp]) : 
    rtr₁ = rtr₂ := by
  induction rtr₁ using Extensional.induction generalizing rtr₂
  case base h₁ => 
    sorry
  case step hi => 
    sorry
  skip

end Equivalent
end ReactorType