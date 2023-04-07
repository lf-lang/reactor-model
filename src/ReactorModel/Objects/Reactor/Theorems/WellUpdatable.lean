import ReactorModel.Objects.Reactor.Theorems.WellFounded

namespace ReactorType 

class WellUpdatable (α) extends LawfulUpdatable α, WellFounded α

variable [WellUpdatable α] {rtr : α}

theorem LawfulUpdatable.equiv : (Updatable.update rtr cpt i f) ≈ rtr := 
  Equivalent.symm (lawful rtr cpt i f).equiv

end ReactorType
