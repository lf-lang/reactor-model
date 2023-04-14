import ReactorModel.Objects.Reactor.Indexable

noncomputable section

namespace ReactorType

class Finite (α) extends Indexable α where
  fin : ∀ (rtr : α) (cpt : Component), rtr[cpt].Finite

namespace Finite

variable [Finite α]

def ids (rtr : α) (cpt : Component) : List cpt.idType :=
  (fin rtr cpt).toFinset.toList 

end Finite
namespace ReactorType