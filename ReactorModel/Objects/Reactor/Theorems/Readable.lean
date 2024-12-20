import ReactorModel.Objects.Reactor.Theorems.Hierarchical
import ReactorModel.Objects.Reactor.Theorems.Extensional

namespace Reactor

class Readable (α) extends Hierarchical α, Extensional α

variable [Readable α] {rtr rtr₁ : α}

-- TODO: For simplification of this proof, see comments above `StrictMember.rtr_equiv`.
theorem LawfulMemUpdate.unique
    (u₁ : LawfulMemUpdate cpt i v rtr rtr₁) (u₂ : LawfulMemUpdate cpt i v rtr rtr₂) :
    rtr₁ = rtr₂ := by
  induction u₁ generalizing rtr₂ <;> cases u₂
  case final.final e₁ _ h₁' _ _ h₂' e₂ =>
    exact RootEqualUpTo.ext (RootEqualUpTo.trans e₁.symm e₂) (h₂' ▸ h₁')
  case nested.nested j₁ _ _ _ _ e₁ h₁ h₁' u₁ hi j₂ _ _ u₂ h₂ h₂' e₂ =>
    have h : j₁ = j₂ := by injection (u₁.member₁.nested h₁).unique (u₂.member₁.nested h₂)
    subst h; cases h₁ ▸ h₂; cases hi u₂
    exact RootEqualUpTo.ext (RootEqualUpTo.trans e₁.symm e₂) <| h₁' ▸ h₂'.symm
  case final.nested h₁ _ _ _ _ u h₂ _ _ =>
    injection (StrictMember.final h₁).unique (u.member₁.nested h₂)
  case nested.final h₁ _ u _ _ h₂ _ _ =>
    injection (StrictMember.final h₂).unique (u.member₁.nested h₁)

theorem LawfulUpdate.unique
    (u₁ : LawfulUpdate cpt i v rtr rtr₁) (u₂ : LawfulUpdate cpt i v rtr rtr₂) : rtr₁ = rtr₂ := by
  cases u₁ <;> cases u₂
  case notMem.notMem => simp_all
  case update.update u₁ u₂ => exact u₁.unique u₂
  all_goals exact ‹IsEmpty _›.elim <| Member.strict ‹LawfulMemUpdate ..›.member₁

end Reactor
