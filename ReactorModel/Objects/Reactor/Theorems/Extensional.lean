import ReactorModel.Objects.Reactor.Extensional

namespace Reactor

variable [Extensional α] {rtr₁ : α}

theorem RootEqualUpTo.ext (e : rtr₁ ≃[cpt][i] rtr₂) (h : rtr₁{cpt}{i} = rtr₂{cpt}{i}) :
    rtr₁ = rtr₂ := by
  ext1; ext1 c; ext1 j; grind

end Reactor
