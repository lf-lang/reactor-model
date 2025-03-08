import Mathlib.Data.Set.Finite.Basic
import ReactorModel.Objects.Reactor.Hierarchical

noncomputable section

namespace Reactor

class Finite (α) [Hierarchical α] where
  fin : ∀ (rtr : α) (cpt : Component), rtr[cpt].Finite

def Finite.ids [Hierarchical α] [Finite α] (rtr : α) (cpt : Component) : List α✦cpt :=
  (fin rtr cpt).toFinset.toList

namespace Reactor
