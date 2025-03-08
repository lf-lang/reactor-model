import ReactorModel.Objects.Reactor.Extensional

namespace Reactor

variable [Extensional α] {rtr₁ : α}

theorem RootEqualUpTo.ext (e : rtr₁ ≃[cpt][i] rtr₂) (h : rtr₁{cpt}{i} = rtr₂{cpt}{i}) :
    rtr₁ = rtr₂ := by
  ext1; ext1 c; ext1 j
  by_cases hc : c = cpt <;> by_cases hj : j = i
  · exact hc ▸ hj ▸ h
  · exact hc ▸ e (.inr hj)
  · exact e (.inl hc)
  · exact e (.inl hc)

end Reactor
