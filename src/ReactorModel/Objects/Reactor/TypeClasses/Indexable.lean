import ReactorModel.Objects.Reactor.TypeClasses.Basic

open Reactor (Component)

namespace ReactorType

class Indexable (α) extends ReactorType α where
  uniqueIDs : ∀ {rtr : α} {cmp i}, Subsingleton (Lineage cmp i rtr)

namespace Indexable

open Classical in
noncomputable def con? [Indexable α] (rtr : α) (cmp : Component) (i : ID) : Option (Identified α) := 
  if l : Nonempty (Lineage cmp i rtr) then l.some.container else none

noncomputable def obj? [inst : ReactorType.Indexable α] (rtr : α) : 
    (cmp : Component) → cmp.idType ⇀ inst.componentType cmp
  | .rcn, i       => con? rtr .rcn i >>= (cmp? .rcn ·.obj i)
  | .prt, i       => con? rtr .prt i >>= (cmp? .prt ·.obj i)
  | .act, i       => con? rtr .act i >>= (cmp? .act ·.obj i)
  | .stv, i       => con? rtr .stv i >>= (cmp? .stv ·.obj i)
  | .rtr, .nest i => con? rtr .rtr i >>= (cmp? .rtr ·.obj i)
  | .rtr, ⊤       => rtr

notation rtr "[" cmp "][" i "]" => ReactorType.Indexable.obj? rtr cmp i
notation rtr "[" cmp "][" i "]&" => ReactorType.Indexable.con? rtr cmp i

variable [Indexable α]

theorem obj?_lift {rtr₁ : α} {cmp o} {j : ID} 
    (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j] = some o) : rtr₁[cmp][j] = some o := by
  sorry

-- Note: By `ho` we get `rtr₂ = rtr₃`.
theorem obj?_lift_root {rtr₁ : α} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[.rtr][⊤] = some rtr₃) : 
    ∃ j, rtr₁[.rtr][j] = some rtr₃ := by
  sorry


end Indexable
end ReactorType