import ReactorModel.Objects.Reactor.Theorems.Equivalent

namespace ReactorType

theorem UniqueIDs.updated [ReactorType.WellFounded α] {rtr₁ rtr₂ : α}
    (u : LawfulUpdate cpt i f rtr₁ rtr₂) (h : UniqueIDs rtr₁) : UniqueIDs rtr₂ where
  allEq m₁ m₂ := open Member in
    h.allEq (.fromLawfulUpdate m₁ u) (.fromLawfulUpdate m₂ u) ▸ Equivalent.from_lawfulUpdate u m₁ 
      |>.trans (Equivalent.from_lawfulUpdate u m₂).symm 
      |>.to_eq

def LawfulMemUpdate.member [ReactorType α] {rtr₁ rtr₂ : α} :
    (LawfulMemUpdate cpt i f rtr₁ rtr₂) → Member cpt i rtr₁
  | final _ h _  => .final $ Partial.mem_iff.mpr ⟨_, h⟩ 
  | nest _ h _ u => .nest h u.member

open Indexable in
theorem LawfulMemUpdate.unique [Indexable α] {rtr rtr₁ rtr₂ : α}
    (u₁ : LawfulMemUpdate cpt i f rtr rtr₁) (u₂ : LawfulMemUpdate cpt i f rtr rtr₂) : 
    rtr₁ = rtr₂ := by
  induction u₁ generalizing rtr₂ <;> cases u₂
  case final.final e₁ h₁ h₁' _ h₂ h₂' e₂ =>
    injection h₁ ▸ h₂ with h
    exact RootEqualUpTo.ext (RootEqualUpTo.trans e₁.symm e₂) (h₂' ▸ h ▸ h₁')
  case nest.nest j₁ _ _ _ _ e₁ h₁ h₁' u₁ hi j₂ _ _ u₂ h₂ h₂' e₂ =>
    have h : j₁ = j₂ := by injection unique_ids.allEq (u₁.member.nest h₁) (u₂.member.nest h₂)
    subst h; cases h₁ ▸ h₂; cases hi u₂
    exact RootEqualUpTo.ext (RootEqualUpTo.trans e₁.symm e₂) $ h₁' ▸ h₂'.symm
  case final.nest h₁ _ _ _ _ u h₂ _ _ =>
    injection unique_ids.allEq (Member.final' h₁) (u.member.nest h₂)
  case nest.final h₁ _ u _ _ h₂ _ _ =>
    injection unique_ids.allEq (Member.final' h₂) (u.member.nest h₁)

-- TODO: Alternative approach to this theorem:
--       Use `obj?_preserved` and `obj?_updated`, as well as an extensionality theorem for `obj?`.
--       That could be more useful in general, too.
open Indexable in
theorem LawfulMemUpdate.ne_comm [Indexable α] {rtr rtr₁ rtr₁' rtr₂ rtr₂' : α} 
    (u₁ : LawfulMemUpdate cpt₁ i₁ f₁ rtr rtr₁) (u₂ : LawfulMemUpdate cpt₂ i₂ f₂ rtr₁ rtr₂) 
    (u₁' : LawfulMemUpdate cpt₂ i₂ f₂ rtr rtr₁') (u₂' : LawfulMemUpdate cpt₁ i₁ f₁ rtr₁' rtr₂') 
    (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂) : rtr₂ = rtr₂' := by
  cases u₁ <;> cases u₂' <;> cases u₁' <;> cases u₂
  case final.final.final.final =>
    sorry
  case final.final.nest.nest =>
    sorry
  case nest.nest.final.final =>
    sorry
  case nest.nest.nest.nest =>
    sorry
  case final.nest h₁ _ _ _ _ _ u₂ h₂ _ _ =>
    sorry -- contradiction by unique_ids.allEq m₁ m₂
  case nest.final h₁ _ _ _ _ _ u₂ h₂ _ _ =>
    sorry -- contradiction by unique_ids.allEq m₁ m₂

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