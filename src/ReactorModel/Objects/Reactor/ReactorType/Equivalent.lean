import ReactorModel.Objects.Reactor.ReactorType.Indexable

namespace ReactorType

structure Equivalent [Indexable α] (rtr₁ rtr₂ : α) : Prop where
  con? : ∀ cmp, rtr₁[cmp]&.map (·.id) = rtr₂[cmp]&.map (·.id)
  rcns : rtr₁[.rcn] = rtr₂[.rcn]

namespace Equivalent

variable [Indexable α]

instance : HasEquiv α where 
  Equiv := Equivalent

@[refl]
protected theorem refl {rtr : α} : rtr ≈ rtr where
  con? _ := rfl
  rcns   := rfl

@[symm]
protected theorem symm {rtr₁ : α} (e : rtr₁ ≈ rtr₂) : rtr₂ ≈ rtr₁ where
  con? cmp := e.con? cmp |>.symm
  rcns     := e.rcns.symm

@[trans]
protected theorem trans {rtr₁ : α} (e₁ : rtr₁ ≈ rtr₂) (e₂ : rtr₂ ≈ rtr₃) : rtr₁ ≈ rtr₃ where
  con? cmp := e₁.con? cmp |>.trans (e₂.con? cmp)
  rcns     := e₁.rcns.trans e₂.rcns

theorem obj?_some_iff {rtr₁ : α} {cmp i} (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, rtr₁[cmp][i] = some o₁) ↔ (∃ o₂, rtr₂[cmp][i] = some o₂) := 
  sorry

theorem obj?_none_iff {rtr₁ : α} {cmp i} (e : rtr₁ ≈ rtr₂) : 
    (rtr₁[cmp][i] = none) ↔ (rtr₂[cmp][i] = none) := by 
  sorry

end Equivalent
end ReactorType