import ReactorModel.Objects.Reactor.Updatable
import Mathlib.Tactic.Set

noncomputable section
open Classical
open Reactor (Component)

namespace ReactorType

def UniqueIDs [ReactorType α] (rtr : α) : Prop :=
  ∀ {cpt i}, Subsingleton (Member cpt i rtr)

class Indexable (α) extends LawfulUpdatable α where
  unique_ids : ∀ {rtr : α}, UniqueIDs rtr

@[ext]
structure Container (α) where
  id  : WithTop ID 
  rtr : α 

instance [Coe α β] : Coe (Container α) (Container β) where
  coe i := { id := i.id, rtr := i.rtr }

namespace Member

variable [LawfulUpdatable α] 

def container {rtr : α} : (Member cpt i rtr) → Container α
  | .nest _ (.nest h l)             => container (.nest h l)
  | .nest (rtr₂ := con) (j := j) .. => { id := j, rtr := con }
  | .final _                        => { id := ⊤, rtr := rtr }

theorem nest_container  {rtr₁ rtr₂ : α} 
    (h : ReactorType.nest rtr₁ i = some rtr₂) (m : Member cpt j rtr₂) : 
    ∃ (k : ID) (con : α), (Member.nest h m).container = ⟨k, con⟩ := by
  induction m generalizing i rtr₁
  case final => simp [container]
  case nest hn _ hi => simp [container, hi hn]

theorem container_eq_root {rtr : α} {m : Member cpt i rtr} (h : m.container = ⟨⊤, con⟩) : 
    rtr = con := by
  induction m generalizing con
  case final => 
    simp [container] at h
    assumption
  case nest hn m _ =>
    have ⟨_, _, _⟩ := nest_container hn m
    simp_all

end Member

namespace Indexable

variable [a : Indexable α]

def con? (rtr : α) (cpt : Component) : ID ⇀ Container α := 
  fun i => if m : Nonempty (Member cpt i rtr) then m.some.container else none

notation rtr "[" cpt "]&"        => ReactorType.Indexable.con? rtr cpt
notation rtr "[" cpt "][" i "]&" => ReactorType.Indexable.con? rtr cpt i

def obj? (rtr : α) : (cpt : Component) → cpt.idType ⇀ a.cptType cpt
  | .val cpt, i        => rtr[.val cpt][i]& >>= fun con => cpt? (.val cpt) con.rtr i
  | .rcn,     i        => rtr[.rcn][i]&     >>= fun con => cpt? .rcn       con.rtr i
  | .rtr,     (i : ID) => rtr[.rtr][i]&     >>= fun con => cpt? .rtr       con.rtr i
  | .rtr,     ⊤        => rtr

notation (priority := 1001) rtr "[" cpt "]" => ReactorType.Indexable.obj? rtr cpt
notation rtr "[" cpt "][" i "]"             => ReactorType.Indexable.obj? rtr cpt i

variable {rtr rtr₁ rtr₂ : α}

end Indexable
end ReactorType