import ReactorModel.Objects.Reactor.Practical
import ReactorModel.Objects.Reactor.Theorems.Accessible
import ReactorModel.Objects.Reactor.Theorems.Proper

namespace ReactorType

instance [Practical α] : Accessible α where
  unique_ids := Practical.toProper.unique_ids

variable [Practical α] {rtr : α}

open Updatable in
theorem LawfulUpdatable.update_ne_comm (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂):
    update (update rtr cpt₁ i₁ f₁) cpt₂ i₂ f₂ = update (update rtr cpt₂ i₂ f₂) cpt₁ i₁ f₁ :=
  LawfulUpdate.ne_comm (lawful ..) (lawful ..) (lawful ..) (lawful ..) h

end ReactorType