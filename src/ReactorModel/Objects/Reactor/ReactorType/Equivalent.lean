import ReactorModel.Objects.Reactor.ReactorType.Indexable

namespace ReactorType

-- TODO: Perhaps find another definition (that also works well with `LawfulUpdatable`). For example,
--       `con?_id_eq` doesn't seem to be useful.
structure Equivalent [Indexable α] (rtr₁ rtr₂ : α) : Prop where
  con?_id_eq : ∀ cmp, rtr₁[cmp]&.map (·.id) = rtr₂[cmp]&.map (·.id)
  rcns_eq    : rtr₁[.rcn] = rtr₂[.rcn]

namespace Equivalent

variable [Indexable α] {rtr rtr₁ : α}

instance : HasEquiv α where 
  Equiv := Equivalent

@[refl]
protected theorem refl : rtr ≈ rtr where
  con?_id_eq _ := rfl
  rcns_eq      := rfl

@[symm]
protected theorem symm (e : rtr₁ ≈ rtr₂) : rtr₂ ≈ rtr₁ where
  con?_id_eq cmp := e.con?_id_eq cmp |>.symm
  rcns_eq        := e.rcns_eq.symm

@[trans]
protected theorem trans (e₁ : rtr₁ ≈ rtr₂) (e₂ : rtr₂ ≈ rtr₃) : rtr₁ ≈ rtr₃ where
  con?_id_eq cmp := e₁.con?_id_eq cmp |>.trans (e₂.con?_id_eq cmp)
  rcns_eq        := e₁.rcns_eq.trans e₂.rcns_eq

theorem mem_obj?_ids_iff {cmp i} (e : rtr₁ ≈ rtr₂) : 
    (i ∈ rtr₁[cmp].ids) ↔ (i ∈ rtr₂[cmp].ids) := by
  sorry

theorem mem_cmp?_ids_iff {cmp} (e : rtr₁ ≈ rtr₂) : 
    (i ∈ (cmp? cmp rtr₁).ids) ↔ (i ∈ (cmp? cmp rtr₂).ids) := by
  sorry

theorem nested (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][i] = some n₁) (h₂ : rtr₂[.rtr][i] = some n₂) : 
    n₁ ≈ n₂ := 
  sorry

theorem nest (e : rtr₁ ≈ rtr₂) (h₁ : nest rtr₁ i = some n₁) (h₂ : nest rtr₂ i = some n₂) : 
    n₁ ≈ n₂ := 
  sorry

theorem nested_rcns_eq (e : rtr₁ ≈ rtr₂) (h : cmp? .rcn rtr₂ i = some o) : cmp? .rcn rtr₁ i = some o :=
  sorry

theorem cmp?_some_iff {cmp i} (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, cmp? cmp rtr₁ i = some o₁) ↔ (∃ o₂, cmp? cmp rtr₂ i = some o₂) := 
  sorry

theorem obj?_some_iff {cmp i} (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, rtr₁[cmp][i] = some o₁) ↔ (∃ o₂, rtr₂[cmp][i] = some o₂) := 
  sorry

theorem obj?_none_iff {cmp i} (e : rtr₁ ≈ rtr₂) : 
    (rtr₁[cmp][i] = none) ↔ (rtr₂[cmp][i] = none) := by 
  sorry

end Equivalent

theorem LawfulUpdate.equiv [Indexable α] {rtr₁ : α} {cmp f} (u : LawfulUpdate cmp i f rtr₁ rtr₂) : 
    rtr₁ ≈ rtr₂ := 
  sorry

end ReactorType