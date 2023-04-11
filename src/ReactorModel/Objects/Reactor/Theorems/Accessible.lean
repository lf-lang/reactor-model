import ReactorModel.Objects.Reactor.Updatable
import ReactorModel.Objects.Reactor.Theorems.WellIndexable
import ReactorModel.Objects.Reactor.Theorems.WellUpdatable

namespace ReactorType

class Accessible (α) extends LawfulUpdatable α, WellFounded α, Indexable α 

namespace LawfulUpdatable

open Updatable LawfulUpdatable Indexable

instance [Accessible α] : WellIndexable α where
  wf := Accessible.wf

instance [Accessible α] : WellUpdatable α where
  wf := Accessible.wf

variable [Accessible α] {rtr : α}

theorem obj?_preserved (h : c ≠ cpt ∨ j ≠ i) : (update rtr cpt i f)[c][j] = rtr[c][j] :=
  lawful rtr cpt i f |>.obj?_preserved h

theorem obj?_preserved_cpt (h : c ≠ cpt := by exact (nomatch ·)) : 
    (update rtr cpt i f)[c][j] = rtr[c][j] :=
  obj?_preserved $ .inl h

theorem obj?_preserved_id {c : Component.Valued} (h : j ≠ i) : 
    (update rtr cpt i f)[c][j] = rtr[c][j] :=
  obj?_preserved $ .inr h

theorem obj?_updated {rtr : α} : (update rtr cpt i f)[cpt][i] = f <$> rtr[cpt][i] :=
  lawful rtr cpt i f |>.obj?_updated

end LawfulUpdatable
end ReactorType