import ReactorModel.Objects.Reactor.Practical
import ReactorModel.Objects.Reactor.Theorems.Accessible
import ReactorModel.Objects.Reactor.Theorems.Proper
import ReactorModel.Objects.Reactor.Theorems.FiniteUpdatable

namespace ReactorType

instance [Practical α] : Accessible α where
  unique_ids := Practical.toProper.unique_ids

instance [Practical α] : FiniteUpdatable α where
  update := Practical.update
  lawful := Practical.lawful

variable [Practical α] {rtr : α}

open Updatable in
theorem LawfulUpdatable.update_ne_comm (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂):
    update (update rtr cpt₁ i₁ v₁) cpt₂ i₂ v₂ = update (update rtr cpt₂ i₂ v₂) cpt₁ i₁ v₁ :=
  LawfulUpdate.ne_comm (lawful ..) (lawful ..) (lawful ..) (lawful ..) h

end ReactorType