import ReactorModel.Objects.Reactor.ReactorType.Equivalent
import Mathlib.Tactic.Set

noncomputable section
open Classical
open Reactor (Component)

namespace ReactorType

def UniqueIDs [ReactorType α] (rtr : α) : Prop :=
  ∀ {cpt i}, Subsingleton (Member cpt i rtr)

theorem UniqueIDs.lift [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} 
    (h : UniqueIDs (rtr : β)) : UniqueIDs rtr where
  allEq m₁ m₂ :=
    h.allEq (.fromLawfulCoe m₁) (.fromLawfulCoe m₂) ▸ Member.Equivalent.from_lawfulCoe m₁ 
      |>.trans (Member.Equivalent.from_lawfulCoe m₂).symm 
      |>.to_eq

theorem UniqueIDs.updated [ReactorType.WellFounded α] {rtr₁ rtr₂ : α}
    (u : LawfulUpdate cpt i f rtr₁ rtr₂) (h : UniqueIDs rtr₁) : UniqueIDs rtr₂ where
  allEq m₁ m₂ := open Member in
    h.allEq (.fromLawfulUpdate m₁ u) (.fromLawfulUpdate m₂ u) ▸ Equivalent.from_lawfulUpdate u m₁ 
      |>.trans (Equivalent.from_lawfulUpdate u m₂).symm 
      |>.to_eq

class Indexable (α) extends LawfulUpdatable α where
  unique_ids : ∀ {rtr : α}, UniqueIDs rtr

namespace Member

variable [LawfulUpdatable α]

def container {rtr : α} : Member cpt i rtr → Identified α
  | .nest _ (.nest h l)             => container (.nest h l)
  | .nest (rtr₂ := con) (j := j) .. => { id := j, obj := con }
  | .final _                        => { id := ⊤, obj := rtr }

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

instance [LawfulUpdatable α] [ind : Indexable β] [LawfulCoe α β] : Indexable α where
  unique_ids := UniqueIDs.lift ind.unique_ids 

variable [a : Indexable α]

def con? (rtr : α) (cpt : Component) : ID ⇀ Identified α := 
  fun i => if m : Nonempty (Member cpt i rtr) then m.some.container else none

notation rtr "[" cpt "]&"        => ReactorType.Indexable.con? rtr cpt
notation rtr "[" cpt "][" i "]&" => ReactorType.Indexable.con? rtr cpt i

def obj? (rtr : α) : (cpt : Component) → cpt.idType ⇀ a.componentType cpt
  | .val cpt, i       => rtr[.val cpt][i]& >>= (cpt? (.val cpt) ·.obj i)
  | .rcn,     i       => rtr[.rcn][i]&     >>= (cpt? .rcn       ·.obj i)
  | .rtr,     .nest i => rtr[.rtr][i]&     >>= (cpt? .rtr       ·.obj i)
  | .rtr,     ⊤       => rtr

notation (priority := 1001) rtr "[" cpt "]" => ReactorType.Indexable.obj? rtr cpt
notation rtr "[" cpt "][" i "]"             => ReactorType.Indexable.obj? rtr cpt i

variable {rtr rtr₁ : α}

def obj' (rtr : α) {cpt : Component} {i : cpt.idType} (h : i ∈ rtr[cpt]) : a.componentType cpt :=
  Partial.mem_ids_iff.mp h |>.choose

notation rtr "⟦" h "⟧" => ReactorType.Indexable.obj' rtr h

theorem obj'_eq_obj? {h : ↑i ∈ rtr[cpt]} : rtr⟦h⟧ = rtr[cpt][i] := by
  rw [obj', ←(Partial.mem_ids_iff.mp h).choose_spec]

theorem con?_eq_some (h : rtr[cpt][i]& = some con) : 
    ∃ m : Member cpt i rtr, m.container = con := by
  simp [con?] at h
  split at h
  case inl n => exists n.some; injection h
  case inr => contradiction

theorem obj?_to_con?_and_cpt? {o} {i : ID} (h : rtr[cpt][i] = some o) :
    ∃ c, (rtr[cpt][i]& = some c) ∧ (cpt? cpt c.obj i = some o) := by
  cases cpt
  all_goals 
    simp [obj?, bind] at h
    assumption

def con' (rtr : α) {cpt : Component} {i : ID} (h : ↑i ∈ rtr[cpt]) : Identified α :=
  obj?_to_con?_and_cpt? (Partial.mem_ids_iff.mp h).choose_spec |>.choose

notation rtr "⟦" h "⟧&" => ReactorType.Indexable.con' rtr h

theorem con'_eq_con? {h : ↑i ∈ rtr[cpt]} : rtr⟦h⟧& = rtr[cpt][i]& := by
  sorry

theorem cpt?_to_con? {o} (h : cpt? cpt rtr i = some o) : rtr[cpt][i]& = some ⟨⊤, rtr⟩ := by
  let m := Member.final (Partial.mem_ids_iff.mpr ⟨_, h⟩)
  simp [con?, Nonempty.intro m, ←a.unique_ids.allEq m, Member.container]

theorem cpt?_to_obj? {o} (h : cpt? cpt rtr i = some o) : rtr[cpt][i] = some o := by
  cases cpt
  all_goals 
    simp [obj?, bind]
    exact ⟨⟨⊤, rtr⟩, cpt?_to_con? h, h⟩ 

theorem con?_nested {c : ID} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cpt][j]& = some ⟨c, con⟩) : 
    rtr₁[cpt][j]& = some ⟨c, con⟩ := by
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

theorem con?_eq_root (h : rtr[cpt][i]& = some ⟨⊤, con⟩) : rtr = con :=
  Member.container_eq_root (con?_eq_some h).choose_spec

theorem obj?_nested {o} {j : ID} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cpt][j] = some o) : 
    rtr₁[cpt][j] = some o := by
  cases cpt <;> try cases j
  all_goals
    simp [obj?, bind]
    have ⟨⟨c, con⟩, hc, ho⟩ := obj?_to_con?_and_cpt? ho 
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
  exact ⟨i, ho ▸ cpt?_to_obj? h⟩

-- This is a version of `obj?_nested`, where we don't restrict `j` to be an `ID`. This makes a 
-- difference when `cpt = .rtr`. Note that if `cpt = .rtr` and `j = ⊤`, then `j' = .nest i`.
theorem obj?_nested' {o j} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cpt][j] = some o) : 
    ∃ j', rtr₁[cpt][j'] = some o := by
  cases cpt <;> try cases j
  case rtr.root => exact obj?_nested_root h ho
  all_goals exact ⟨_, obj?_nested h ho⟩

theorem obj?_mem_ids_nested {cpt : Component.Valued} 
    (h : nest rtr₁ i = some rtr₂) (hm : j ∈ rtr₂[cpt].ids) : j ∈ rtr₁[cpt].ids :=
  Partial.mem_ids_iff.mpr ⟨_, obj?_nested h (Partial.mem_ids_iff.mp hm).choose_spec⟩  

theorem member_isEmpty_con?_none (h : IsEmpty (Member cpt i rtr)) : rtr[cpt][i]& = none := by
  cases cpt <;> simp [con?, not_nonempty_iff.mpr h]

theorem member_isEmpty_obj?_none (h : IsEmpty (Member cpt i rtr)) : rtr[cpt][i] = none := by
  cases cpt <;> simp [obj?, member_isEmpty_con?_none h, bind]

end Indexable

namespace LawfulCoe

variable [a : Indexable α] [b : Indexable β] [c : LawfulCoe α β] {rtr : α}

theorem lower_container_eq {m : Member cpt i rtr} (h : m.container = con) : 
    (m : Member cpt i (rtr : β)).container = ↑con := by
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

theorem lower_con?_some (h : rtr[cpt][i]& = some con) : (rtr : β)[cpt][i]& = some ↑con := by
  simp [Indexable.con?] at h ⊢
  split at h
  case inr => contradiction 
  case inl n =>
    injection h with h
    simp [←c.lower_container_eq h, (⟨n.some⟩ : Nonempty (Member cpt i (rtr : β)))]
    congr
    apply b.unique_ids.allEq

theorem lower_obj?_some {i o} (h : rtr[cpt][i] = some o) : (rtr : β)[cpt][i] = some ↑o := by
  cases cpt <;> try cases i
  case rtr.root => simp_all [Indexable.obj?]
  all_goals
    have ⟨_, h₁, h₂⟩ := a.obj?_to_con?_and_cpt? h
    simp [Indexable.obj?, bind, c.lower_con?_some h₁, c.lower_cpt?_eq_some _ h₂]

theorem lower_mem_obj?_ids {i} (h : i ∈ rtr[cpt].ids) : i ∈ (rtr : β)[cpt].ids :=
  Partial.mem_ids_iff.mpr ⟨_, c.lower_obj?_some (Partial.mem_ids_iff.mp h).choose_spec⟩ 

end LawfulCoe

open Indexable Updatable

namespace LawfulMemUpdate

variable [Indexable α] {rtr₁ : α}

theorem obj?_preserved (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) (h : c ≠ cpt ∨ j ≠ i) : 
    rtr₂[c][j] = rtr₁[c][j] := by
  -- TODO: We need to somehow distinguish whether [c][j] even identifies a component, and if so, 
  --       whether it lives in the same reactor as [cpt][i].
  induction u
  case final e _ _ =>
    have := e (c := c) (j := j) (by simp [h])
    sorry
  case nest =>
    sorry

theorem obj?_some₁ (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : ∃ o, rtr₁[cpt][i] = some o := by
  induction u 
  case final         => exact ⟨_, cpt?_to_obj? ‹_›⟩
  case nest h _ _ hi => exact ⟨_, obj?_nested h hi.choose_spec⟩

theorem obj?_some₂ (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : ∃ o, rtr₂[cpt][i] = some o := by
  induction u 
  case final       => exact ⟨_, cpt?_to_obj? ‹_›⟩
  case nest h _ hi => exact ⟨_, obj?_nested h hi.choose_spec⟩

theorem obj?_updated (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    rtr₂[cpt][i] = f <$> rtr₁[cpt][i] := by
  induction u
  case final h₁ h₂ => 
    rw [cpt?_to_obj? h₁, cpt?_to_obj? h₂, Option.map_some]
  case nest h₁ h₂ u hi =>
    have ⟨_, h₁'⟩ := u.obj?_some₁
    have ⟨_, h₂'⟩ := u.obj?_some₂
    rw [obj?_nested h₁ h₁', obj?_nested h₂ h₂']
    exact h₁' ▸ h₂' ▸ hi

end LawfulMemUpdate

namespace LawfulUpdate

variable [Indexable α] {rtr₁ : α}

theorem obj?_preserved (h : c ≠ cpt ∨ j ≠ i) : 
    (LawfulUpdate cpt i f rtr₁ rtr₂) → rtr₂[c][j] = rtr₁[c][j]
  | update u   => u.obj?_preserved h
  | notMem _ h => h ▸ rfl

theorem obj?_updated : (LawfulUpdate cpt i f rtr₁ rtr₂) → rtr₂[cpt][i] = f <$> rtr₁[cpt][i]
  | update u => u.obj?_updated
  | notMem h e => by subst e; have h := member_isEmpty_obj?_none h; simp at h; simp [h]

end LawfulUpdate

namespace LawfulUpdatable

variable [Indexable α] {rtr : α}

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

namespace Equivalent

variable [Indexable α] {rtr₁ : α}

theorem obj?_rcn_eq (e : rtr₁ ≈ rtr₂) : rtr₁[.rcn] = rtr₂[.rcn] :=
  sorry

theorem mem_obj?_ids_iff {i} (e : rtr₁ ≈ rtr₂) : (i ∈ rtr₁[cpt].ids) ↔ (i ∈ rtr₂[cpt].ids) := by
  sorry

theorem obj?_rtr_equiv (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][i] = some n₁) (h₂ : rtr₂[.rtr][i] = some n₂) : 
    n₁ ≈ n₂ := by
  sorry

theorem obj?_some_iff (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, rtr₁[cpt][i] = some o₁) ↔ (∃ o₂, rtr₂[cpt][i] = some o₂) := 
  sorry

end Equivalent
end ReactorType