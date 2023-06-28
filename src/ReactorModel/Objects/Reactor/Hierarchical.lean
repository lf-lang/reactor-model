import ReactorModel.Objects.Reactor.Basic

noncomputable section
open Classical

namespace Reactor

def UniqueIDs [Reactor α] (rtr : α) : Prop :=
  ∀ {cpt i}, Subsingleton (Member cpt i rtr)

class Hierarchical (α) extends Reactor α where
  unique_ids : ∀ {rtr : α}, UniqueIDs rtr

def Hierarchical.obj? [Hierarchical α] (rtr : α) (cpt : Component) : cpt.idType ⇀ cpt.type α :=
  fun i => if h : ∃ o, Object rtr cpt i o then h.choose else none

notation (priority := 1001) rtr "[" cpt "]" => Hierarchical.obj? rtr cpt
notation rtr "[" cpt "][" i "]"             => Hierarchical.obj? rtr cpt i 

end Reactor