import ReactorModel.Execution

open Classical

structure ChangeListEquiv (cs₁ cs₂ : List (Identified Change)) : Prop where
  ports   : ∀ i,   cs₁.lastSome? (·.obj.portValue? i)     = cs₂.lastSome? (·.obj.portValue? i)
  state   : ∀ i,   cs₁.lastSome? (·.obj.stateValue? i)    = cs₂.lastSome? (·.obj.stateValue? i)
  actions : ∀ i t, cs₁.filterMap (·.obj.actionValue? i t) = cs₂.filterMap (·.obj.actionValue? i t)
  -- NOTE: Mutations are currently noops, and can therefore be ignored.

notation cs₁:max " ⋈ " cs₂:max => ChangeListEquiv cs₁ cs₂

theorem ChangeListEquiv.refl (cs) : cs ⋈ cs := {
  ports := λ _ => rfl,
  state := λ _ => rfl,
  actions := λ _ _ => rfl
}