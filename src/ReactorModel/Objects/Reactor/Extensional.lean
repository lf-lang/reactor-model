import ReactorModel.Objects.Reactor.Basic

namespace ReactorType

class Extensional (α) extends ReactorType α where
  ext_iff : (rtr₁ = rtr₂) ↔ (get? rtr₁ = get? rtr₂)
  
variable [Extensional α] {rtr₁ rtr₂ : α}

@[ext]
theorem Extensional.ext : (get? rtr₁ = get? rtr₂) → rtr₁ = rtr₂ :=
  ext_iff.mpr

namespace ReactorType