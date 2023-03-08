import ReactorModel.Objects.Reactor.ReactorType.Basic

open Reactor (Component)

namespace ReactorType

class Indexable (α) extends ReactorType α where
  uniqueIDs : ∀ {rtr : α}, UniqueIDs rtr

namespace Indexable

instance [ReactorType α] [ind : Indexable β] [ReactorType.LawfulCoe α β] : Indexable α where
  uniqueIDs := UniqueIDs.lift ind.uniqueIDs 

def _root_.ReactorType.Lineage.container [ReactorType α] {cmp} {rtr : α} :
    Lineage cmp i rtr → Identified α
  | .nest _ (.nest h l)             => container (.nest h l)
  | .nest (rtr₁ := con) (j := j) .. => { id := j, obj := con }
  | _                               => { id := ⊤, obj := rtr }

open Classical in
noncomputable def con? [Indexable α] (rtr : α) (cmp : Component) (i : ID) : Option (Identified α) := 
  if l : Nonempty (Lineage cmp i rtr) then l.some.container else none

noncomputable def obj? [ind : ReactorType.Indexable α] (rtr : α) : 
    (cmp : Component) → cmp.idType ⇀ ind.componentType cmp
  | .rcn, i       => con? rtr .rcn i >>= (cmp? .rcn ·.obj i)
  | .prt, i       => con? rtr .prt i >>= (cmp? .prt ·.obj i)
  | .act, i       => con? rtr .act i >>= (cmp? .act ·.obj i)
  | .stv, i       => con? rtr .stv i >>= (cmp? .stv ·.obj i)
  | .rtr, .nest i => con? rtr .rtr i >>= (cmp? .rtr ·.obj i)
  | .rtr, ⊤       => rtr

notation rtr "[" cmp "][" i "]" => ReactorType.Indexable.obj? rtr cmp i
notation rtr "[" cmp "][" i "]&" => ReactorType.Indexable.con? rtr cmp i

end Indexable

instance [ReactorType α] [ReactorType β] [c : ReactorType.LawfulCoe α β] {rtr : α} {cmp} :
    Coe (Lineage cmp i rtr) (Lineage cmp i (rtr : β)) where
  coe := Lineage.fromLawfulCoe

theorem LawfulCoe.lower_container_eq
    [Indexable α] [Indexable β] [ReactorType.LawfulCoe α β] {cmp} {rtr : α} {l : Lineage cmp i rtr}
    (h : l.container = con) : (l : Lineage cmp i (rtr : β)).container = ↑con := by
  sorry

theorem LawfulCoe.lower_con?_some 
    [Indexable α] [Indexable β] [c : ReactorType.LawfulCoe α β] {rtr : α} {cmp} 
    (h : rtr[cmp][i]& = some con) : (rtr : β)[cmp][i]& = some ↑con := by
  sorry

theorem LawfulCoe.lower_obj?_some 
    [Indexable α] [b : Indexable β] [ReactorType.LawfulCoe α β] {rtr : α} {cmp} {i o} 
    (h : rtr[cmp][i] = some o) : (rtr : β)[cmp][i] = some ↑o := by
  sorry

namespace Indexable

variable [Indexable α]

theorem obj?_nested {rtr₁ : α} {cmp o} {j : ID} 
    (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j] = some o) : rtr₁[cmp][j] = some o := by
  sorry

-- This is a version of `obj?_nested`, where we don't restrict `j` to be an `ID`. This makes a 
-- difference when `cmp = .rtr`. Note that if `cmp = .rtr` and `j = ⊤`, then `j' = .nest i`.
theorem obj?_nested' {rtr₁ : α} {cmp o j}
    (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j] = some o) : ∃ j', rtr₁[cmp][j'] = some o := by
  sorry

-- Note: By `ho` we get `rtr₂ = rtr₃`.
theorem obj?_nested_root {rtr₁ : α} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[.rtr][⊤] = some rtr₃) : 
    ∃ j, rtr₁[.rtr][j] = some rtr₃ := by
  sorry

end Indexable
end ReactorType