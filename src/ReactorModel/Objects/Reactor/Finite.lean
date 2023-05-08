import ReactorModel.Objects.Reactor.Indexable

noncomputable section

namespace ReactorType

class Finite (α) [Indexable α] where
  fin : ∀ (rtr : α) (cpt : Component), rtr[cpt].Finite

def Finite.ids [Indexable α] [Finite α] (rtr : α) (cpt : Component) : List cpt.idType :=
  (fin rtr cpt).toFinset.toList 

namespace ReactorType