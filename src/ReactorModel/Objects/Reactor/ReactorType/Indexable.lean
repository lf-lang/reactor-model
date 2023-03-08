import ReactorModel.Objects.Reactor.ReactorType.Basic

open Reactor (Component)

namespace ReactorType

class Indexable (α) extends ReactorType α where
  uniqueIDs : ∀ {rtr : α}, UniqueIDs rtr

namespace Indexable

instance [ReactorType α] [ind : Indexable β] [LawfulCoe α β] : Indexable α where
  uniqueIDs := UniqueIDs.lift ind.uniqueIDs 

def _root_.ReactorType.Lineage.container [ReactorType α] {cmp} {rtr : α} :
    Lineage cmp i rtr → Identified α
  | .nest _ (.nest h l)             => container (.nest h l)
  | .nest (rtr₁ := con) (j := j) .. => { id := j, obj := con }
  | _                               => { id := ⊤, obj := rtr }

open Classical in
noncomputable def con? [Indexable α] (rtr : α) (cmp : Component) (i : ID) : Option (Identified α) := 
  if l : Nonempty (Lineage cmp i rtr) then l.some.container else none

notation rtr "[" cmp "][" i "]&" => ReactorType.Indexable.con? rtr cmp i

noncomputable def obj? [ind : ReactorType.Indexable α] (rtr : α) : 
    (cmp : Component) → cmp.idType ⇀ ind.componentType cmp
  | .rcn, i       => rtr[.rcn][i]& >>= (cmp? .rcn ·.obj i)
  | .prt, i       => rtr[.prt][i]& >>= (cmp? .prt ·.obj i)
  | .act, i       => rtr[.act][i]& >>= (cmp? .act ·.obj i)
  | .stv, i       => rtr[.stv][i]& >>= (cmp? .stv ·.obj i)
  | .rtr, .nest i => rtr[.rtr][i]& >>= (cmp? .rtr ·.obj i)
  | .rtr, ⊤       => rtr

notation rtr "[" cmp "][" i "]" => ReactorType.Indexable.obj? rtr cmp i

variable [a : Indexable α]

theorem obj?_to_con?_and_cmp? {rtr : α} {cmp} {o} {i : ID} (h : rtr[cmp][i] = some o) :
    ∃ c, (rtr[cmp][i]& = some c) ∧ (cmp? cmp c.obj i = some o) := by
  cases cmp
  all_goals 
    simp [obj?, bind] at h
    assumption

theorem cmp?_to_con? {rtr : α} {cmp} {o} (h : cmp? cmp rtr i = some o) : 
    rtr[cmp][i]& = some ⟨⊤, rtr⟩ := by
  let l := Lineage.final (Partial.mem_ids_iff.mpr ⟨_, h⟩)
  simp [con?, Nonempty.intro l, ←a.uniqueIDs.allEq l, Lineage.container]

theorem cmp?_to_obj? {rtr : α} {cmp} {o} (h : cmp? cmp rtr i = some o) : rtr[cmp][i] = some o := by
  cases cmp
  all_goals 
    simp [obj?, bind]
    exact ⟨⟨⊤, rtr⟩, cmp?_to_con? h, h⟩ 

set_option pp.proofs.withType false
theorem con?_nested {rtr₁ : α} {cmp} {j : ID} 
    (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j]& = some con) : rtr₁[cmp][j]& = some con := by
  simp [con?] at ho ⊢
  split at ho
  case inr => contradiction
  case inl n =>
    have ⟨l₂⟩ := n
    let l₁ := Lineage.nest h l₂
    simp [←a.uniqueIDs.allEq l₂] at ho
    simp [Nonempty.intro l₁, ←a.uniqueIDs.allEq l₁, ←ho]
    cases h₂ : l₂
    case nest => simp [h₂, Lineage.container] 
    case final h =>
      -- This case must hold a contradiction.
      -- Otherwise `j` would have to be `⊤` which isn't possible by `j : ID`.
      sorry 
    
theorem obj?_nested {rtr₁ : α} {cmp o} {j : ID} 
    (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j] = some o) : rtr₁[cmp][j] = some o := by
  cases cmp <;> try cases j
  all_goals
    simp [obj?, bind]
    have ⟨c, hc, ho⟩ := obj?_to_con?_and_cmp? ho 
    have := con?_nested h hc
    exists c

-- Note: By `ho` we get `rtr₂ = rtr₃`.
theorem obj?_nested_root {rtr₁ : α} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[.rtr][⊤] = some rtr₃) : 
    ∃ j, rtr₁[.rtr][j] = some rtr₃ := by
  simp [obj?] at ho
  exact ⟨i, ho ▸ cmp?_to_obj? h⟩

-- This is a version of `obj?_nested`, where we don't restrict `j` to be an `ID`. This makes a 
-- difference when `cmp = .rtr`. Note that if `cmp = .rtr` and `j = ⊤`, then `j' = .nest i`.
theorem obj?_nested' {rtr₁ : α} {cmp o j}
    (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j] = some o) : ∃ j', rtr₁[cmp][j'] = some o := by
  cases cmp <;> try cases j
  case rtr.root => exact obj?_nested_root h ho
  all_goals exact ⟨_, obj?_nested h ho⟩

end Indexable

instance [ReactorType α] [ReactorType β] [c : LawfulCoe α β] {rtr : α} {cmp} :
    Coe (Lineage cmp i rtr) (Lineage cmp i (rtr : β)) where
  coe := Lineage.fromLawfulCoe

theorem LawfulCoe.lower_container_eq
    [Indexable α] [Indexable β] [LawfulCoe α β] {cmp} {rtr : α} {l : Lineage cmp i rtr}
    (h : l.container = con) : (l : Lineage cmp i (rtr : β)).container = ↑con := by
  induction l
  case final =>
    simp [Lineage.container] at h ⊢
    simp [←h]
  case nest l _ => 
    cases l 
    case final => 
      sorry
    case nest hi =>
      sorry

theorem LawfulCoe.lower_con?_some [Indexable α] [b : Indexable β] [c : LawfulCoe α β] {rtr : α} {cmp} 
    (h : rtr[cmp][i]& = some con) : (rtr : β)[cmp][i]& = some ↑con := by
  simp [Indexable.con?] at h ⊢
  split at h
  case inr => contradiction 
  case inl n =>
    injection h with h
    simp [←c.lower_container_eq h, (⟨n.some⟩ : Nonempty (Lineage cmp i (rtr : β)))]
    congr
    apply b.uniqueIDs.allEq

theorem LawfulCoe.lower_obj?_some 
    [a : Indexable α] [b : Indexable β] [c : LawfulCoe α β] {rtr : α} {cmp} {i o} 
    (h : rtr[cmp][i] = some o) : (rtr : β)[cmp][i] = some ↑o := by
  cases cmp <;> try cases i
  case rtr.root => simp_all [Indexable.obj?]
  all_goals
    have ⟨_, h₁, h₂⟩ := a.obj?_to_con?_and_cmp? h
    simp [Indexable.obj?, bind, c.lower_con?_some h₁, c.lower_cmp?_eq_some _ h₂]

end ReactorType