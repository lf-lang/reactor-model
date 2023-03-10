import ReactorModel.Objects.Reactor.ReactorType.Basic

open Reactor (Component)

namespace ReactorType

class Indexable (α) extends ReactorType α where
  uniqueIDs : ∀ {rtr : α}, UniqueIDs rtr

namespace Lineage

def container [ReactorType α] {cmp} {rtr : α} :
    Lineage cmp i rtr → Identified α
  | .nest _ (.nest h l)             => container (.nest h l)
  | .nest (rtr₂ := con) (j := j) .. => { id := j, obj := con }
  | .final _                        => { id := ⊤, obj := rtr }

theorem nest_container [ReactorType α] {cmp} {rtr₁ rtr₂ : α} 
    (h : ReactorType.nest rtr₁ i = some rtr₂) (l : Lineage cmp j rtr₂) : 
    ∃ (k : ID) (con : α), (Lineage.nest h l).container = ⟨k, con⟩ := by
  induction l generalizing i rtr₁
  case final => simp [container]
  case nest hn _ hi => simp [container, hi hn]

theorem container_eq_root [ReactorType α] {cmp} {rtr : α}
    {l : Lineage cmp i rtr} (h : l.container = ⟨⊤, con⟩) : rtr = con := by
  induction l generalizing con
  case final => 
    simp [container] at h
    assumption
  case nest hn l _ =>
    have ⟨_, _, _⟩ := nest_container hn l
    simp_all

end Lineage

namespace Indexable

instance [ReactorType α] [ind : Indexable β] [LawfulCoe α β] : Indexable α where
  uniqueIDs := UniqueIDs.lift ind.uniqueIDs 

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

theorem con?_eq_some {rtr : α} {cmp} (h : rtr[cmp][i]& = some con) : 
    ∃ l : Lineage cmp i rtr, l.container = con := by
  simp [con?] at h
  split at h
  case inl n => exists n.some; injection h
  case inr => contradiction

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

theorem con?_nested {rtr₁ : α} {cmp} {c : ID}
    (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j]& = some ⟨c, con⟩) : 
    rtr₁[cmp][j]& = some ⟨c, con⟩ := by
  simp [con?] at ho ⊢ 
  split at ho
  case inr => contradiction
  case inl n =>
    set l := n.some
    cases hl : l
    case final hc =>
      simp [hl, Lineage.container] at ho
    case nest l₂ h₂ =>
      let l₁ := Lineage.nest h (.nest h₂ l₂)
      simp [hl, Lineage.container] at ho
      simp [Nonempty.intro l₁, ←a.uniqueIDs.allEq l₁, Lineage.container, ho]

theorem con?_eq_root {rtr : α} {cmp} (h : rtr[cmp][i]& = some ⟨⊤, con⟩) : rtr = con :=
  Lineage.container_eq_root (con?_eq_some h).choose_spec

theorem obj?_nested {rtr₁ : α} {cmp o} {j : ID} 
    (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j] = some o) : rtr₁[cmp][j] = some o := by
  cases cmp <;> try cases j
  all_goals
    simp [obj?, bind]
    have ⟨⟨c, con⟩, hc, ho⟩ := obj?_to_con?_and_cmp? ho 
    cases c
    case nest c => 
      have := con?_nested h hc
      exists ⟨c, con⟩
    case root => 
      replace hc := con?_eq_root hc
      simp at ho
      subst hc
      exists ⟨i, rtr₂⟩
      let l := Lineage.nest h (.final $ Partial.mem_ids_iff.mpr ⟨_, ho⟩)
      simp [ho, con?, Nonempty.intro l, ←a.uniqueIDs.allEq l, Lineage.container]

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
  case nest l hi => 
    cases l 
    case final => 
      simp [Lineage.fromLawfulCoe, Lineage.container] at h ⊢
      simp [← h] 
    case nest hi =>
      simp [Lineage.container] at h
      simp [←hi h, Lineage.fromLawfulCoe, Lineage.container]

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