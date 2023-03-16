import ReactorModel.Objects.Reactor.ReactorType.Updatable

open Reactor (Component)

namespace ReactorType

def UniqueIDs [ReactorType α] (rtr : α) : Prop :=
  ∀ {cmp i}, Subsingleton (Member cmp i rtr)

theorem UniqueIDs.lift [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} 
    (h : UniqueIDs (rtr : β)) : UniqueIDs rtr where
  allEq l₁ l₂ :=
    h.allEq (.fromLawfulCoe l₁) (.fromLawfulCoe l₂) ▸ Member.Equivalent.from_lawfulCoe l₁ 
      |>.trans (Member.Equivalent.from_lawfulCoe l₂).symm 
      |>.to_eq

theorem UniqueIDs.updated [ReactorType α] {rtr₁ rtr₂ : α} {cmp i f} 
    (u : LawfulUpdate cmp i f rtr₁ rtr₂) (h : UniqueIDs rtr₁) : UniqueIDs rtr₂ where
  allEq l₁ l₂ := open Member in
    h.allEq (.fromLawfulUpdate u l₁) (.fromLawfulUpdate u l₂) ▸ Equivalent.from_lawfulUpdate u l₁ 
      |>.trans (Equivalent.from_lawfulUpdate u l₂).symm 
      |>.to_eq

class Indexable (α) extends Extensional α where
  unique_ids : ∀ {rtr : α}, UniqueIDs rtr

namespace Member

variable [Extensional α] {cmp}

def container {rtr : α} : Member cmp i rtr → Identified α
  | .nest _ (.nest h l)             => container (.nest h l)
  | .nest (rtr₂ := con) (j := j) .. => { id := j, obj := con }
  | .final _                        => { id := ⊤, obj := rtr }

theorem nest_container  {rtr₁ rtr₂ : α} 
    (h : ReactorType.nest rtr₁ i = some rtr₂) (m : Member cmp j rtr₂) : 
    ∃ (k : ID) (con : α), (Member.nest h m).container = ⟨k, con⟩ := by
  induction m generalizing i rtr₁
  case final => simp [container]
  case nest hn _ hi => simp [container, hi hn]

theorem container_eq_root {rtr : α} {m : Member cmp i rtr} (h : m.container = ⟨⊤, con⟩) : 
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

instance [Extensional α] [ind : Indexable β] [LawfulCoe α β] : Indexable α where
  unique_ids := UniqueIDs.lift ind.unique_ids 

open Classical in
noncomputable def con? [Indexable α] (rtr : α) (cmp : Component) : ID ⇀ Identified α := 
  fun i => if m : Nonempty (Member cmp i rtr) then m.some.container else none

notation rtr "[" cmp "]&"        => ReactorType.Indexable.con? rtr cmp
notation rtr "[" cmp "][" i "]&" => ReactorType.Indexable.con? rtr cmp i

noncomputable def obj? [a : Indexable α] (rtr : α) : 
    (cmp : Component) → cmp.idType ⇀ a.componentType cmp
  | .val cmp, i       => rtr[.val cmp][i]& >>= (cmp? (.val cmp) ·.obj i)
  | .rcn,     i       => rtr[.rcn][i]&     >>= (cmp? .rcn       ·.obj i)
  | .rtr,     .nest i => rtr[.rtr][i]&     >>= (cmp? .rtr       ·.obj i)
  | .rtr,     ⊤       => rtr

notation (priority := 1001) rtr "[" cmp "]" => ReactorType.Indexable.obj? rtr cmp
notation rtr "[" cmp "][" i "]"             => ReactorType.Indexable.obj? rtr cmp i

variable [a : Indexable α] {cmp : Component} {rtr rtr₁ : α}

theorem con?_eq_some (h : rtr[cmp][i]& = some con) : 
    ∃ m : Member cmp i rtr, m.container = con := by
  simp [con?] at h
  split at h
  case inl n => exists n.some; injection h
  case inr => contradiction

theorem obj?_to_con?_and_cmp? {o} {i : ID} (h : rtr[cmp][i] = some o) :
    ∃ c, (rtr[cmp][i]& = some c) ∧ (cmp? cmp c.obj i = some o) := by
  cases cmp
  all_goals 
    simp [obj?, bind] at h
    assumption

theorem cmp?_to_con? {o} (h : cmp? cmp rtr i = some o) : rtr[cmp][i]& = some ⟨⊤, rtr⟩ := by
  let m := Member.final (Partial.mem_ids_iff.mpr ⟨_, h⟩)
  simp [con?, Nonempty.intro m, ←a.unique_ids.allEq m, Member.container]

theorem cmp?_to_obj? {o} (h : cmp? cmp rtr i = some o) : rtr[cmp][i] = some o := by
  cases cmp
  all_goals 
    simp [obj?, bind]
    exact ⟨⟨⊤, rtr⟩, cmp?_to_con? h, h⟩ 

theorem con?_nested {c : ID} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j]& = some ⟨c, con⟩) : 
    rtr₁[cmp][j]& = some ⟨c, con⟩ := by
  simp [con?] at ho ⊢ 
  split at ho
  case inr => contradiction
  case inl n =>
    set m := n.some
    cases hm : m
    case final hc =>
      simp [hm, Member.container] at ho
    case nest l₂ h₂ =>
      let l₁ := Member.nest h (.nest h₂ l₂)
      simp [hm, Member.container] at ho
      simp [Nonempty.intro l₁, ←a.unique_ids.allEq l₁, Member.container, ho]

theorem con?_eq_root (h : rtr[cmp][i]& = some ⟨⊤, con⟩) : rtr = con :=
  Member.container_eq_root (con?_eq_some h).choose_spec

theorem obj?_nested {o} {j : ID} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j] = some o) : 
    rtr₁[cmp][j] = some o := by
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
      let m := Member.nest h (.final $ Partial.mem_ids_iff.mpr ⟨_, ho⟩)
      simp [ho, con?, Nonempty.intro m, ←a.unique_ids.allEq m, Member.container]

-- Note: By `ho` we get `rtr₂ = rtr₃`.
theorem obj?_nested_root (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[.rtr][⊤] = some rtr₃) : 
    ∃ j, rtr₁[.rtr][j] = some rtr₃ := by
  simp [obj?] at ho
  exact ⟨i, ho ▸ cmp?_to_obj? h⟩

-- This is a version of `obj?_nested`, where we don't restrict `j` to be an `ID`. This makes a 
-- difference when `cmp = .rtr`. Note that if `cmp = .rtr` and `j = ⊤`, then `j' = .nest i`.
theorem obj?_nested' {o j} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j] = some o) : 
    ∃ j', rtr₁[cmp][j'] = some o := by
  cases cmp <;> try cases j
  case rtr.root => exact obj?_nested_root h ho
  all_goals exact ⟨_, obj?_nested h ho⟩

theorem obj?_mem_ids_nested {cmp : Component.Valued} 
    (h : nest rtr₁ i = some rtr₂) (hm : j ∈ rtr₂[cmp].ids) : j ∈ rtr₁[cmp].ids :=
  Partial.mem_ids_iff.mpr ⟨_, obj?_nested h (Partial.mem_ids_iff.mp hm).choose_spec⟩  

theorem member_isEmpty_con?_none (h : IsEmpty (Member cmp i rtr)) : rtr[cmp][i]& = none := by
  cases cmp <;> simp [con?, not_nonempty_iff.mpr h]

theorem member_isEmpty_obj?_none (h : IsEmpty (Member cmp i rtr)) : rtr[cmp][i] = none := by
  cases cmp <;> simp [obj?, member_isEmpty_con?_none h, bind]

end Indexable

namespace LawfulCoe

variable [a : Indexable α] [b : Indexable β] [c : LawfulCoe α β] {cmp : Component} {rtr : α}

theorem lower_container_eq {m : Member cmp i rtr} (h : m.container = con) : 
    (m : Member cmp i (rtr : β)).container = ↑con := by
  induction m
  case final =>
    simp [Member.container] at h ⊢
    simp [←h]
  case nest m hi => 
    cases m 
    case final => 
      simp [Member.fromLawfulCoe, Member.container] at h ⊢
      simp [← h] 
    case nest hi =>
      simp [Member.container] at h
      simp [←hi h, Member.fromLawfulCoe, Member.container]

theorem lower_con?_some (h : rtr[cmp][i]& = some con) : (rtr : β)[cmp][i]& = some ↑con := by
  simp [Indexable.con?] at h ⊢
  split at h
  case inr => contradiction 
  case inl n =>
    injection h with h
    simp [←c.lower_container_eq h, (⟨n.some⟩ : Nonempty (Member cmp i (rtr : β)))]
    congr
    apply b.unique_ids.allEq

theorem lower_obj?_some {i o} (h : rtr[cmp][i] = some o) : (rtr : β)[cmp][i] = some ↑o := by
  cases cmp <;> try cases i
  case rtr.root => simp_all [Indexable.obj?]
  all_goals
    have ⟨_, h₁, h₂⟩ := a.obj?_to_con?_and_cmp? h
    simp [Indexable.obj?, bind, c.lower_con?_some h₁, c.lower_cmp?_eq_some _ h₂]

theorem lower_mem_obj?_ids {i} (h : i ∈ rtr[cmp].ids) : i ∈ (rtr : β)[cmp].ids :=
  Partial.mem_ids_iff.mpr ⟨_, c.lower_obj?_some (Partial.mem_ids_iff.mp h).choose_spec⟩ 

end LawfulCoe

open Indexable Updatable

namespace LawfulMemUpdate

variable [Indexable α] {rtr₁ : α}

theorem obj?_preserved {cmp f} (u : LawfulMemUpdate cmp i f rtr₁ rtr₂) (h : c ≠ cmp ∨ j ≠ i) : 
    rtr₂[c][j] = rtr₁[c][j] := by
  -- TODO: We need to somehow distinguish whether [c][j] even identifies a component, and if so, 
  --       whether it lives in the same reactor as [cmp][i].
  induction u
  case final e _ _ =>
    have := e (c := c) (j := j) (by simp [h])
    sorry
  case nest =>
    sorry

theorem obj?_some₁ {cmp f} (u : LawfulMemUpdate cmp i f rtr₁ rtr₂) : 
    ∃ o, rtr₁[cmp][i] = some o := by
  induction u 
  case final         => exact ⟨_, cmp?_to_obj? ‹_›⟩
  case nest h _ _ hi => exact ⟨_, obj?_nested h hi.choose_spec⟩

theorem obj?_some₂ {cmp f} (u : LawfulMemUpdate cmp i f rtr₁ rtr₂) : 
    ∃ o, rtr₂[cmp][i] = some o := by
  induction u 
  case final       => exact ⟨_, cmp?_to_obj? ‹_›⟩
  case nest h _ hi => exact ⟨_, obj?_nested h hi.choose_spec⟩

theorem obj?_updated {cmp f} (u : LawfulMemUpdate cmp i f rtr₁ rtr₂) : 
    rtr₂[cmp][i] = f <$> rtr₁[cmp][i] := by
  induction u
  case final h₁ h₂ => 
    rw [cmp?_to_obj? h₁, cmp?_to_obj? h₂, Option.map_some]
  case nest h₁ h₂ u hi =>
    have ⟨_, h₁'⟩ := u.obj?_some₁
    have ⟨_, h₂'⟩ := u.obj?_some₂
    rw [obj?_nested h₁ h₁', obj?_nested h₂ h₂']
    exact h₁' ▸ h₂' ▸ hi

end LawfulMemUpdate

namespace LawfulUpdate

variable [Indexable α] {rtr₁ : α}

theorem obj?_preserved {cmp f} (h : c ≠ cmp ∨ j ≠ i) : 
    (LawfulUpdate cmp i f rtr₁ rtr₂) → rtr₂[c][j] = rtr₁[c][j]
  | update u => u.obj?_preserved h
  | notMem _ => rfl

theorem obj?_updated {cmp f} : (LawfulUpdate cmp i f rtr₁ rtr₂) → rtr₂[cmp][i] = f <$> rtr₁[cmp][i]
  | update u => u.obj?_updated
  | notMem h => by have h := member_isEmpty_obj?_none h; simp at h; simp [h]

end LawfulUpdate

namespace LawfulUpdatable

-- TODO: We need this to handle a type class diamond. What is the proper way to fix this?
private class LawfulUpdexable (α) extends Indexable α, LawfulUpdatable α  

variable [LawfulUpdexable α] {rtr : α}

theorem obj?_preserved {cmp f} (h : c ≠ cmp ∨ j ≠ i) : (update rtr cmp i f)[c][j] = rtr[c][j] :=
  lawful rtr cmp i f |>.obj?_preserved h

theorem obj?_preserved_cmp {cmp f} (h : c ≠ cmp) : (update rtr cmp i f)[c][j] = rtr[c][j] :=
  obj?_preserved $ .inl h

theorem obj?_preserved_id {cmp f} {c : Component.Valued} (h : j ≠ i) : 
    (update rtr cmp i f)[c][j] = rtr[c][j] :=
  obj?_preserved $ .inr h

theorem obj?_updated {cmp f} : (update rtr cmp i f)[cmp][i] = f <$> rtr[cmp][i] :=
  lawful rtr cmp i f |>.obj?_updated

end LawfulUpdatable
end ReactorType