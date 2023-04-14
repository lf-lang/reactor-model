import ReactorModel.Objects.Reactor.WellFounded
import ReactorModel.Objects.Reactor.Updatable
import ReactorModel.Objects.Reactor.Indexable
import ReactorModel.Objects.Reactor.Theorems.Basic

noncomputable section
open Classical

namespace ReactorType
namespace StrictMember

variable [WellFounded α] {rtr rtr₁ : α}

namespace Equivalent

-- TODO: Adjust the definition of Member Equivalence to include a refl case, so you can remove the 
--       requirement of wellfoundedness. Then you can also move all of the theorems below.
@[refl]
theorem refl (s : StrictMember cpt i rtr) : Equivalent s s := by
  induction rtr using WellFounded.induction
  case nested hi =>
    cases s
    case final    => exact final
    case nested h => exact nested _ _ (hi _ ⟨_, h⟩ _)

instance : Equivalence (Equivalent (· : StrictMember cpt i rtr) ·) := 
  { refl, symm, trans }

theorem fromLawfulMemUpdate (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) (s : StrictMember c j rtr₂) : 
    Equivalent s (s.fromLawfulMemUpdate u) := by
  induction u <;> cases s <;> (simp [StrictMember.fromLawfulMemUpdate]; try exact final)
  case final.nested e _ _ _ _ _ hn => exact nested hn (e (c := .rtr) (.inl $ by simp) ▸ hn) (refl _)
  case nested.nested e h₁ h₂ _ hi _ _ m hn =>
    split
    case inl hj => cases hj; cases Option.some_inj.mp $ h₂ ▸ hn; exact nested hn h₁ (hi m)
    case inr hj => exact nested hn (hn ▸ e (.inr hj)) (refl _)

theorem fromLawfulUpdate (u : LawfulUpdate cpt i f rtr₁ rtr₂) (s : StrictMember c j rtr₂) : 
    Equivalent s (s.fromLawfulUpdate u) := by
  cases u
  case notMem   => cases ‹_ = _›; rfl
  case update u => exact Equivalent.fromLawfulMemUpdate u s 

end Equivalent
end StrictMember

namespace Member

variable [WellFounded α] {rtr rtr₁ : α}

namespace Equivalent

@[refl]
theorem refl : (m : Member cpt i rtr) → Equivalent m m
  | .root     => root
  | .strict s => strict $ .refl s
  
instance : Equivalence (Equivalent (· : Member cpt i rtr) ·) := 
  { refl, symm, trans }

theorem fromLawfulMemUpdate (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    (m : Member c j rtr₂) → Equivalent m (m.fromLawfulMemUpdate u)
  | .root     => root
  | .strict s => strict $ .fromLawfulMemUpdate u s 

theorem fromLawfulUpdate (u : LawfulUpdate cpt i f rtr₁ rtr₂) :
    (m : Member c j rtr₂) → Equivalent m (m.fromLawfulUpdate u)
  | .root     => root
  | .strict s => strict $ .fromLawfulUpdate u s 

end Equivalent
end Member

namespace UniqueIDs

variable [WellFounded α] {rtr₁ : α}

theorem updated 
    (u : LawfulUpdate cpt i f rtr₁ rtr₂) (h : UniqueIDs rtr₁) : UniqueIDs rtr₂ where
  allEq m₁ m₂ := open Member in
    h.allEq (.fromLawfulUpdate m₁ u) (.fromLawfulUpdate m₂ u) ▸ Equivalent.fromLawfulUpdate u m₁ 
      |>.trans (Equivalent.fromLawfulUpdate u m₂).symm 
      |>.to_eq

end UniqueIDs
end ReactorType