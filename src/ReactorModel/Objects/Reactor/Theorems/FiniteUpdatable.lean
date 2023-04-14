import ReactorModel.Objects.Reactor.Practical
import ReactorModel.Objects.Reactor.Theorems.Indexable

noncomputable section

namespace ReactorType

class FiniteUpdatable (α) extends Finite α, LawfulUpdatable α

instance [Practical α] : FiniteUpdatable α where
  update := Practical.update
  lawful := Practical.lawful

namespace FiniteUpdatable

variable [FiniteUpdatable α]

def update' (rtr : α) (cpt : Component.Valued) (v : cpt.type) : α :=
  go rtr cpt v $ Finite.ids rtr cpt
where 
  go (rtr : α) (cpt : Component.Valued) (v : cpt.type) : List ID → α
  | [] => rtr
  | hd :: tl => go (update rtr cpt hd fun _ => v) cpt v tl

variable {rtr : α} 

theorem update'.go_equiv (ids : List ID) : rtr ≈ update'.go rtr cpt v ids := by
  induction ids generalizing rtr <;> simp [go]
  case nil     => exact .refl _
  case cons hi => exact Equivalent.trans LawfulUpdatable.equiv hi

theorem update'_equiv : rtr ≈ update' rtr cpt v :=
  update'.go_equiv _

end FiniteUpdatable
end ReactorType