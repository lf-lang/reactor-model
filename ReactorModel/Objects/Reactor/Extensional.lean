import ReactorModel.Objects.Reactor.Basic

namespace Reactor

class Extensional (α) extends Reactor α where
  ext_iff : (rtr₁ = rtr₂) ↔ (get? rtr₁ = get? rtr₂)

variable [Extensional α] {rtr₁ rtr₂ : α}

@[ext]
theorem Extensional.ext : (get? rtr₁ = get? rtr₂) → rtr₁ = rtr₂ :=
  ext_iff.mpr

namespace Reactor
