import ReactorModel.Objects.Reactor.Basic

noncomputable section
open Classical

namespace ReactorType

def UniqueIDs [ReactorType α] (rtr : α) : Prop :=
  ∀ {cpt i}, Subsingleton (Member cpt i rtr)

class Indexable (α) extends ReactorType α where
  unique_ids : ∀ {rtr : α}, UniqueIDs rtr

def Indexable.obj? [Indexable α] (rtr : α) (cpt : Cpt α) : cpt.idType ⇀ cpt.type α :=
  fun i => if h : ∃ o, Object rtr cpt i o then h.choose else none

notation (priority := 1001) rtr "[" cpt "]" => Indexable.obj? rtr cpt
notation rtr "[" cpt "][" i "]"             => Indexable.obj? rtr cpt i 

end ReactorType