import ReactorModel.Objects.Reactor.Theorems.Equivalent

namespace ReactorType

theorem UniqueIDs.updated [ReactorType.WellFounded α] {rtr₁ rtr₂ : α}
    (u : LawfulUpdate cpt i f rtr₁ rtr₂) (h : UniqueIDs rtr₁) : UniqueIDs rtr₂ where
  allEq m₁ m₂ := open Member in
    h.allEq (.fromLawfulUpdate m₁ u) (.fromLawfulUpdate m₂ u) ▸ Equivalent.from_lawfulUpdate u m₁ 
      |>.trans (Equivalent.from_lawfulUpdate u m₂).symm 
      |>.to_eq

theorem LawfulMemUpdate.member₁ [ReactorType α] {rtr₁ rtr₂ : α}
    (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : Member cpt i rtr₁ :=
  sorry

theorem LawfulMemUpdate.member₂ [ReactorType α] {rtr₁ rtr₂ : α}
    (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : Member cpt i rtr₂ :=
  sorry -- by u.member₁ and u.equiv

theorem LawfulUpdate.ne_comm [ReactorType α] {rtr rtr₁ rtr₁' rtr₂ rtr₂' : α} 
    (u₁ : LawfulUpdate cpt₁ i₁ f₁ rtr rtr₁) (u₂ : LawfulUpdate cpt₂ i₂ f₂ rtr₁ rtr₂) 
    (u₁' : LawfulUpdate cpt₂ i₂ f₂ rtr rtr₁') (u₂' : LawfulUpdate cpt₁ i₁ f₁ rtr₁' rtr₂') 
    (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂) : rtr₂ = rtr₂' := by
  cases u₁ <;> cases u₂' <;> cases u₂ <;> cases u₁'
  case update.update.update.notMem =>
    exact IsEmpty.elim ‹_› $ sorry
    -- have := LawfulMemUpdate.member ‹_›  
  all_goals sorry -- The only cases that should remain have matching kind on u₁&u₂' and u₂&u₁':
            -- nnnn, nnuu, uunn, uuuu
  -- Can you prove this without extensionality?

open Updatable in
theorem LawfulUpdatable.update_ne_comm [LawfulUpdatable α] {rtr : α} (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂):
    update (update rtr cpt₁ i₁ f₁) cpt₂ i₂ f₂ = update (update rtr cpt₂ i₂ f₂) cpt₁ i₁ f₁ :=
  LawfulUpdate.ne_comm (lawful ..) (lawful ..) (lawful ..) (lawful ..) h
  
end ReactorType