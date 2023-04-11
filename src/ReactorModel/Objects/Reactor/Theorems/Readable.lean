import ReactorModel.Objects.Reactor.Theorems.Indexable
import ReactorModel.Objects.Reactor.Theorems.Extensional

namespace ReactorType

class Readable (α) extends Indexable α, Extensional α  

namespace LawfulMemUpdate

variable [Readable α] {rtr : α}

theorem unique 
    (u₁ : LawfulMemUpdate cpt i f rtr rtr₁) (u₂ : LawfulMemUpdate cpt i f rtr rtr₂) : 
    rtr₁ = rtr₂ := by
  induction u₁ generalizing rtr₂ <;> cases u₂
  case final.final e₁ h₁ h₁' _ h₂ h₂' e₂ =>
    injection h₁ ▸ h₂ with h
    exact RootEqualUpTo.ext (RootEqualUpTo.trans e₁.symm e₂) (h₂' ▸ h ▸ h₁')
  case nest.nest j₁ _ _ _ _ e₁ h₁ h₁' u₁ hi j₂ _ _ u₂ h₂ h₂' e₂ =>
    have h : j₁ = j₂ := by injection (u₁.member₁.nested h₁).unique (u₂.member₁.nested h₂)
    subst h; cases h₁ ▸ h₂; cases hi u₂
    exact RootEqualUpTo.ext (RootEqualUpTo.trans e₁.symm e₂) $ h₁' ▸ h₂'.symm
  case final.nest h₁ _ _ _ _ u h₂ _ _ =>
    injection (StrictMember.final h₁).unique (u.member₁.nested h₂)
  case nest.final h₁ _ u _ _ h₂ _ _ =>
    injection (StrictMember.final h₂).unique (u.member₁.nested h₁)

end LawfulMemUpdate

theorem LawfulUpdate.ne_comm [Indexable α] {rtr rtr₁ rtr₁' rtr₂ rtr₂' : α} 
    (u₁ : LawfulUpdate cpt₁ i₁ f₁ rtr rtr₁) (u₂ : LawfulUpdate cpt₂ i₂ f₂ rtr₁ rtr₂) 
    (u₁' : LawfulUpdate cpt₂ i₂ f₂ rtr rtr₁') (u₂' : LawfulUpdate cpt₁ i₁ f₁ rtr₁' rtr₂') 
    (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂) : rtr₂ = rtr₂' := by
  -- Use `obj?_preserved` and `obj?_updated`, as well as an extensionality theorem for `obj?`.
  sorry
  
end ReactorType