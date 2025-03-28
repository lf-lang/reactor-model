import Mathlib.Data.Set.Finite.Basic
import ReactorModel.Objects.Reactor.Hierarchical

noncomputable section

namespace Reactor

class Finite (α) [Hierarchical α] where
  fin : ∀ (rtr : α) (cpt : Component), rtr[cpt].Finite

def Finite.ids [Hierarchical α] [Finite α] (rtr : α) (cpt : Component) : List α✦cpt :=
  (fin rtr cpt).toFinset.toList

def Finite.card [Hierarchical α] [Finite α] (rtr : α) (cpt : Component) : Nat :=
  (fin rtr cpt).toFinset.card

notation rtr "#" cpt:max => Finite.card rtr cpt

namespace Reactor
