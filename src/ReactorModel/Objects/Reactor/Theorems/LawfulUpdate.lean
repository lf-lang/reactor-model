import ReactorModel.Objects.Reactor.Theorems.Equivalent

namespace ReactorType

theorem UniqueIDs.updated [ReactorType.WellFounded α] {rtr₁ rtr₂ : α}
    (u : LawfulUpdate cpt i f rtr₁ rtr₂) (h : UniqueIDs rtr₁) : UniqueIDs rtr₂ where
  allEq m₁ m₂ := open Member in
    h.allEq (.fromLawfulUpdate m₁ u) (.fromLawfulUpdate m₂ u) ▸ Equivalent.from_lawfulUpdate u m₁ 
      |>.trans (Equivalent.from_lawfulUpdate u m₂).symm 
      |>.to_eq

def LawfulMemUpdate.member [ReactorType α] {rtr₁ rtr₂ : α}
    (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : Member cpt i rtr₁ :=
  sorry

def LawfulMemUpdate.unique [Indexable α] {rtr rtr₁ rtr₂ : α}
    (u₁ : LawfulMemUpdate cpt i f rtr rtr₁) (u₂ : LawfulMemUpdate cpt i f rtr rtr₂) : rtr₁ = rtr₂ := 
  sorry 

theorem LawfulMemUpdate.ne_comm [Indexable α] {rtr rtr₁ rtr₁' rtr₂ rtr₂' : α} 
    (u₁ : LawfulMemUpdate cpt₁ i₁ f₁ rtr rtr₁) (u₂ : LawfulMemUpdate cpt₂ i₂ f₂ rtr₁ rtr₂) 
    (u₁' : LawfulMemUpdate cpt₂ i₂ f₂ rtr rtr₁') (u₂' : LawfulMemUpdate cpt₁ i₁ f₁ rtr₁' rtr₂') 
    (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂) : rtr₂ = rtr₂' := by
  sorry

theorem LawfulUpdate.ne_comm [Indexable α] {rtr rtr₁ rtr₁' rtr₂ rtr₂' : α} 
    (u₁ : LawfulUpdate cpt₁ i₁ f₁ rtr rtr₁) (u₂ : LawfulUpdate cpt₂ i₂ f₂ rtr₁ rtr₂) 
    (u₁' : LawfulUpdate cpt₂ i₂ f₂ rtr rtr₁') (u₂' : LawfulUpdate cpt₁ i₁ f₁ rtr₁' rtr₂') 
    (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂) : rtr₂ = rtr₂' := by
  cases u₁ <;> cases u₂' <;> cases u₁' <;> cases u₂ <;> repeat subst ‹_ = _›
  case update.update.update.update u₁ u₂' u₁' u₂ => exact LawfulMemUpdate.ne_comm u₁ u₂ u₁' u₂' h
  case notMem.notMem.notMem.notMem => rfl
  case notMem.notMem.update.update => exact LawfulMemUpdate.unique ‹_› ‹_› 
  case update.update.notMem.notMem => exact LawfulMemUpdate.unique ‹_› ‹_› 
  all_goals first 
    | exact IsEmpty.elim ‹_› $ LawfulMemUpdate.member ‹_›
    | refine IsEmpty.elim ‹_› ?_
      try exact LawfulMemUpdate.member ‹_›
      try exact .fromEquiv (LawfulMemUpdate.equiv ‹_›) $ LawfulMemUpdate.member ‹_›
  case update.update.notMem.update u' _ u  _ => exact .fromEquiv (Equivalent.symm u'.equiv) u.member
  case notMem.update.update.update _  u u' _ => exact .fromEquiv (Equivalent.symm u'.equiv) u.member

open Updatable in
theorem LawfulUpdatable.update_ne_comm [Indexable α] {rtr : α} (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂):
    update (update rtr cpt₁ i₁ f₁) cpt₂ i₂ f₂ = update (update rtr cpt₂ i₂ f₂) cpt₁ i₁ f₁ :=
  LawfulUpdate.ne_comm (lawful ..) (lawful ..) (lawful ..) (lawful ..) h
  
end ReactorType