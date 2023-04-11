import ReactorModel.Objects.Reactor.WellFounded
import ReactorModel.Objects.Reactor.Updatable
import ReactorModel.Objects.Reactor.Indexable
import ReactorModel.Objects.Reactor.Theorems.Basic

noncomputable section
open Classical

namespace ReactorType
namespace Equivalent

variable [WellFounded α]

@[refl]
theorem refl (rtr : α) : rtr ≈ rtr := by
  induction rtr using WellFounded.induction
  case nest hi =>
    constructor <;> (intros; simp_all)
    exact hi _ _ ‹_›  

instance : Equivalence ((· : α) ≈ ·) := 
  { refl, symm, trans }

end Equivalent

theorem LawfulMemUpdate.equiv [WellFounded α] {rtr₁ : α}
    (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : rtr₁ ≈ rtr₂ := by
  induction u <;> constructor
  case final.mem_get?_iff e h₁ h₂ =>
    intro c j
    by_cases hc : c = cpt <;> try subst hc
    case neg => exact e.mem_iff (.inl hc)
    case pos =>
      by_cases hj : j = i <;> try subst hj
      case neg => exact e.mem_iff (.inr hj)
      case pos => simp [Partial.mem_iff, h₁, h₂]
  case final.get?_rcn_some_eq e _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rcn) (j := j) (.inl $ by simp)
    simp_all
  case final.get?_rtr_some_equiv e _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rtr) (j := j) (.inl $ by simp)
    simp_all
    apply Equivalent.refl
  case nest.mem_get?_iff j _ _ _ _ e h₁ h₂ _ _ =>
    intro c j'
    by_cases hc : c = .rtr <;> try subst hc
    case neg => exact e.mem_iff (.inl hc)
    case pos => 
      by_cases hj : j' = j <;> try subst hj
      case neg => exact e.mem_iff (.inr hj)
      case pos => simp [Partial.mem_iff, h₁, h₂]
  case nest.get?_rcn_some_eq e h₁ h₂ _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rcn) (j := j) (.inl $ by simp)
    simp_all
  case nest.get?_rtr_some_equiv j _ _ _ _ e _ _ _ hi =>
    intro j' n₁' n₂' h₁' h₂'
    by_cases hj : j' = j <;> try subst hj
    case pos => simp_all; assumption
    case neg => 
      have := e (c := .rtr) (j := j') (.inr hj)
      simp_all
      apply Equivalent.refl

theorem LawfulUpdate.equiv [WellFounded α] {rtr₁ : α} :
    (LawfulUpdate cpt i f rtr₁ rtr₂) → rtr₁ ≈ rtr₂
  | notMem _ h => h ▸ (.refl _)
  | update u   => u.equiv

namespace StrictMember

variable [WellFounded α] {rtr rtr₁ : α}

def fromLawfulMemUpdate {rtr₁ : α} : 
    (StrictMember c j rtr₂) → (LawfulMemUpdate cpt i f rtr₁ rtr₂) → StrictMember c j rtr₁
  | final h, u => final' $ (Equivalent.get?_some_iff u.equiv).mpr ⟨_, h⟩
  | nested h s, .final e _ _ => nested (h ▸ e (.inl $ by simp)) s 
  | nested h s (j := j₂), .nest e h₁ h₂ u (j := j₁) =>
      if hj : j₂ = j₁ 
      then nested h₁ $ fromLawfulMemUpdate ((Option.some_inj.mp $ h₂ ▸ hj ▸ h) ▸ s) u
      else nested (h ▸ e $ .inr hj) s 

def fromLawfulUpdate (s : StrictMember c j rtr₂) : 
    (LawfulUpdate cpt i f rtr₁ rtr₂) → StrictMember c j rtr₁
  | .notMem _ h => h ▸ s
  | .update u   => s.fromLawfulMemUpdate u

namespace Equivalent

@[refl]
theorem refl (s : StrictMember cpt i rtr) : Equivalent s s := by
  induction rtr using WellFounded.induction
  case nest hi =>
    cases s
    case final    => exact final
    case nested h => exact nested _ _ (hi _ ⟨_, h⟩ _)

instance : Equivalence (Equivalent (· : StrictMember cpt i rtr) ·) := 
  { refl, symm, trans }

theorem fromLawfulMemUpdate (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) (s : StrictMember c j rtr₂) : 
    Equivalent s (s.fromLawfulMemUpdate u) := by
  induction u <;> cases s <;> (simp [StrictMember.fromLawfulMemUpdate]; try exact final)
  case final.nested e _ _ _ _ _ hn => exact nested hn (e (c := .rtr) (.inl $ by simp) ▸ hn) (refl _)
  case nest.nested e h₁ h₂ _ hi _ _ m hn =>
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

-- TODO: All of the definitions/theorems in this namespace could be lifted pretty mechanically from
--       `StrictMember`.
namespace Member

variable [WellFounded α] {rtr rtr₁ : α}

def fromLawfulMemUpdate (m : Member c j rtr₂) (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    Member c j rtr₁ :=
  match m with
  | root => root 
  | strict s => s.fromLawfulMemUpdate u

def fromLawfulUpdate (m : Member c j rtr₂) (u : LawfulUpdate cpt i f rtr₁ rtr₂) : Member c j rtr₁ :=
  match m with
  | root => root
  | strict s => s.fromLawfulUpdate u

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