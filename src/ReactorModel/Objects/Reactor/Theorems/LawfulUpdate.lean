import ReactorModel.Objects.Reactor.Theorems.Equivalent

namespace ReactorType

theorem UniqueIDs.updated [ReactorType.WellFounded α] {rtr₁ rtr₂ : α}
    (u : LawfulUpdate cpt i f rtr₁ rtr₂) (h : UniqueIDs rtr₁) : UniqueIDs rtr₂ where
  allEq m₁ m₂ := open Member in
    h.allEq (.fromLawfulUpdate m₁ u) (.fromLawfulUpdate m₂ u) ▸ Equivalent.from_lawfulUpdate u m₁ 
      |>.trans (Equivalent.from_lawfulUpdate u m₂).symm 
      |>.to_eq

open Updatable in
theorem LawfulUpdatable.update_ne_comm [LawfulUpdatable α] {rtr : α} (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂):
    update (update rtr cpt₁ i₁ f₁) cpt₂ i₂ f₂ = update (update rtr cpt₂ i₂ f₂) cpt₁ i₁ f₁ :=
  sorry

end ReactorType