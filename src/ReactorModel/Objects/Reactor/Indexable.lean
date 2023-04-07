import ReactorModel.Objects.Reactor.Basic

noncomputable section
open Classical

namespace ReactorType

def UniqueIDs [ReactorType α] (rtr : α) : Prop :=
  ∀ {cpt i}, Subsingleton (Member cpt i rtr)

class Indexable (α) extends ReactorType α where
  unique_ids : ∀ {rtr : α}, UniqueIDs rtr

namespace Indexable

variable [Indexable α]

def obj? (rtr : α) (cpt : Component) : cpt.idType ⇀ cpt.type α :=
  fun i => if h : ∃ o, Object rtr cpt i o then h.choose else none

notation (priority := 1001) rtr "[" cpt "]" => obj? rtr cpt
notation rtr "[" cpt "][" i "]"             => obj? rtr cpt i 

def con? (rtr : α) (cpt : Component) : ID ⇀ Container α := 
  fun i => if s : Nonempty (StrictMember cpt i rtr) then s.some.container else none

notation rtr "[" cpt "]&"        => con? rtr cpt
notation rtr "[" cpt "][" i "]&" => con? rtr cpt i

end Indexable
end ReactorType