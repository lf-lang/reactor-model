import ReactorModel.Objects.Reactor.Indexable
import ReactorModel.Objects.Reactor.Updatable
import ReactorModel.Objects.Reactor.Theorems.Basic

namespace ReactorType
namespace Object

open Indexable
variable [Indexable α] {rtr : α}

theorem unique : (Object rtr cpt i o₁) → (Object rtr cpt i o₂) → o₁ = o₂
  | intro m₁, intro m₂ => unique_ids.allEq m₁ m₂ ▸ rfl

theorem iff_obj?_some : (Object rtr cpt i o) ↔ (rtr[cpt][i] = some o) where
  mp := by 
    intro ⟨m⟩
    simp [obj?]
    split
    case inl h =>
      have ⟨m', h'⟩ := Object.def.mp h.choose_spec
      simp [←h', unique_ids.allEq m m']
    case inr h =>
      push_neg at h
      specialize h m.object
      simp [Object.def] at h
  mpr h := by
    simp [obj?] at h
    split at h
    case inr => contradiction
    case inl h h' => 
      have ⟨m', h'⟩ := Object.def.mp h'.choose_spec
      exact Option.some_inj.mp h ▸ h' ▸ intro m'

theorem not_iff_obj?_none : (∀ o, ¬Object rtr cpt i o) ↔ (rtr[cpt][i] = none) := by
  simp [Option.eq_none_iff_forall_not_mem, iff_obj?_some]

end Object

namespace Indexable

variable [Indexable α] {rtr : α}

theorem get?_some_to_obj?_some (h : get? rtr cpt i = some o) : rtr[cpt][i] = some o :=
  Object.iff_obj?_some.mp (.intro $ .final h)

theorem obj?_root_some (ho : rtr[.rtr][⊤] = some o) : o = rtr := by
  sorry

-- Note: This theorem does not hold for `i' = ⊤`. For a version that supports this case see 
--       `obj?_some_nested'`.
theorem obj?_some_nested {i' : ID} (h : get? rtr .rtr i = some rtr') (ho : rtr'[cpt][i'] = some o) : 
    rtr[cpt][i'] = some o := by
  have ⟨s, h'⟩ := Object.strict_elim $ Object.iff_obj?_some.mpr ho
  exact Object.iff_obj?_some.mp $ h' ▸ .intro (.nested h s)

theorem obj?_some_nested' (h : get? rtr .rtr i = some rtr') (ho : rtr'[cpt][i'] = some o) : 
    ∃ j, rtr[cpt][j] = some o := by
  cases cpt <;> try cases i'
  case rtr.none =>
    exists i
    exact Object.iff_obj?_some.mp $ obj?_root_some ho ▸ (.intro $ .final h)
  all_goals 
    exact ⟨_, obj?_some_nested h ho⟩ 

theorem member_isEmpty_obj?_none (h : IsEmpty $ Member cpt i rtr) : rtr[cpt][i] = none :=
  Object.not_iff_obj?_none.mp (Object.not_of_member_isEmpty h ·)

end Indexable

/-
theorem nest_container {rtr₁ rtr₂ : α} 
    (h : cpt? rtr₁ .rtr i = some rtr₂) (m : Member cpt j rtr₂) : 
    ∃ (k : ID) (con : α), (Member.nested h m).container = ⟨k, con⟩ := by
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

-- TODO: This doesn't just apply to root.
theorem container_eq_root_to_cpt? {rtr : α} {m : Member cpt i rtr} (h : m.container = ⟨⊤, con⟩) : 
    ∃ o, cpt? cpt con i = some o :=
  sorry

namespace ReactorType
namespace Indexable

variable [a : Indexable α] {rtr rtr₁ rtr₂ : α}

theorem con?_eq_some (h : rtr[cpt][i]& = some con) : 
    ∃ m : Member cpt i rtr, m.container = con := by
  simp [con?] at h
  split at h
  case inl n => exists n.some; injection h
  case inr => contradiction

theorem con?_to_obj?_and_cpt? (h : rtr[cpt][i]& = some ⟨c, con⟩) :
    (rtr[.rtr][c] = con) ∧ ∃ o, (cpt? cpt con i = some o) := by
  have ⟨m, hm⟩ := con?_eq_some h
  cases c
  case none => simp [obj?, Member.container_eq_root hm, Member.container_eq_root_to_cpt? hm]
  case some => sorry

theorem obj?_to_con?_and_cpt? {o} {i : ID} (h : rtr[cpt][i] = some o) :
    ∃ c, (rtr[cpt][i]& = some c) ∧ (cpt? cpt c.rtr i = some o) := by
  cases cpt
  all_goals 
    simp [obj?, bind] at h
    assumption

theorem obj?_con?_eq {i₁ i₂ : ID}
    (h₁ : rtr[cpt][i₁] = some rcn₁) (h₂ : rtr[cpt][i₂] = some rcn₂) 
    (hc : rtr[cpt][i₁]& = rtr[cpt][i₂]&) :
    ∃ c con, (rtr[.rtr][c] = some con) ∧ (cpt? cpt con i₁ = some rcn₁) ∧ (cpt? cpt con i₂ = some rcn₂) := by
  have ⟨con₁, hc₁, hr₁⟩ := obj?_to_con?_and_cpt? h₁
  have ⟨con₂, hc₂, hr₂⟩ := obj?_to_con?_and_cpt? h₂
  exists con₁.id, con₁.rtr
  have ⟨ho₁, _, _⟩ := con?_to_obj?_and_cpt? hc₁
  exact ⟨ho₁, hr₁, (Option.some_inj.mp $ hc₂ ▸ hc ▸ hc₁) ▸ hr₂⟩ 

theorem con?_eq_ext 
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂)
    (hc : {c₁ c₂ : Container α} → (rtr[.rtr][c₁.id] = c₁.rtr) → (rtr[.rtr][c₂.id] = c₂.rtr) → 
          (rcns c₁.rtr i₁ = some rcn₁) → (rcns c₂.rtr i₂ = some rcn₂) → c₁.id = c₂.id) : 
    rtr[.rcn][i₁]& = rtr[.rcn][i₂]& := by
  have ⟨c₁, hc₁, hr₁⟩ := obj?_to_con?_and_cpt? h₁
  have ⟨c₂, hc₂, hr₂⟩ := obj?_to_con?_and_cpt? h₂
  simp [hc₁, hc₂]
  have ⟨hc₁, _⟩ := con?_to_obj?_and_cpt? hc₁
  have ⟨hc₂, _⟩ := con?_to_obj?_and_cpt? hc₂
  have hc := hc hc₁ hc₂ hr₁ hr₂
  exact Container.ext _ _ hc $ Option.some_inj.mp (hc₂ ▸ hc ▸ hc₁.symm)

theorem obj?_rtr_and_cpt?_to_obj? (ho : rtr[.rtr][c] = some con) (hc : cpt? cpt con i = some o) :
    rtr[cpt][i] = some o := by
  sorry

theorem cpt?_to_con? {o} (h : cpt? cpt rtr i = some o) : rtr[cpt][i]& = some ⟨⊤, rtr⟩ := by
  let m := Member.final (Partial.mem_iff.mpr ⟨_, h⟩)
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
    case some c => 
      have := con?_nested h hc
      exists ⟨c, con⟩
    case none => 
      replace hc := con?_eq_root hc
      simp at ho
      subst hc
      exists ⟨i, rtr₂⟩
      let m := Member.nest h (.final $ Partial.mem_iff.mpr ⟨_, ho⟩)
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
  case rtr.none => exact obj?_nested_root h ho
  all_goals exact ⟨_, obj?_nested h ho⟩

theorem obj?_mem_nested {j : ID} (h : nest rtr₁ i = some rtr₂) (hm : ↑j ∈ rtr₂[cpt]) : 
    ↑j ∈ rtr₁[cpt] :=
  Partial.mem_iff.mpr ⟨_, obj?_nested h (Partial.mem_iff.mp hm).choose_spec⟩  

theorem mem_cpt?_rtr_eq (ho₁ : rtr[.rtr][c₁] = some con₁) (ho₂ : rtr[.rtr][c₂] = some con₂) 
    (hc₁ : j ∈ cpt? cpt con₁) (hc₂ : j ∈ cpt? cpt con₂) : c₁ = c₂ := by
  cases c₁ <;> cases c₂
  case none.none => rfl
  case none.some c₂ => 
    simp [obj?] at ho₁
    subst ho₁
    let m₁ := Member.final hc₁
    have ⟨con₂', h, h'⟩ := obj?_to_con?_and_cpt? ho₂
    have ⟨m, _⟩ := con?_eq_some h
    -- let m₂ := Member.nest h' m
    sorry
  case some.none => sorry
  case some.some =>
    -- TODO: We can build two `Member` instances here.
    --       One from ho₁ and hc₁ and one from ho₂ and hc₂.
    --       By `unique_ids` they are equal, from which we can extract that `c₁ = c₂`.
    --       The main difficulty is building the `Member` instances.
    sorry

theorem member_isEmpty_con?_none (h : IsEmpty (Member cpt i rtr)) : rtr[cpt][i]& = none := by
  cases cpt <;> simp [con?, not_nonempty_iff.mpr h]

theorem member_isEmpty_obj?_none (h : IsEmpty (Member cpt i rtr)) : rtr[cpt][i] = none := by
  cases cpt <;> simp [obj?, member_isEmpty_con?_none h, bind]

end Indexable
-/

namespace Equivalent

variable [Indexable α] {rtr₁ : α}

theorem obj?_rcn_eq (e : rtr₁ ≈ rtr₂) : rtr₁[.rcn] = rtr₂[.rcn] :=
  sorry

theorem mem_iff {i} (e : rtr₁ ≈ rtr₂) : (i ∈ rtr₁[cpt]) ↔ (i ∈ rtr₂[cpt]) := by
  sorry

theorem obj?_rtr_equiv (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][i] = some n₁) (h₂ : rtr₂[.rtr][i] = some n₂) : 
    n₁ ≈ n₂ := by
  sorry

theorem obj?_some_iff (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, rtr₁[cpt][i] = some o₁) ↔ (∃ o₂, rtr₂[cpt][i] = some o₂) := 
  sorry

end Equivalent

namespace LawfulMemUpdate

open Indexable
variable [a : Indexable α] {rtr₁ : α}

theorem obj?_some₁ (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : ∃ o, rtr₁[cpt][i] = some o := by
  induction u 
  case final         => exact ⟨_, get?_some_to_obj?_some ‹_›⟩
  case nest h _ _ hi => exact ⟨_, obj?_some_nested h hi.choose_spec⟩

theorem obj?_some₂ (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : ∃ o, rtr₂[cpt][i] = some o := by
  induction u 
  case final       => exact ⟨_, get?_some_to_obj?_some ‹_›⟩
  case nest h _ hi => exact ⟨_, obj?_some_nested h hi.choose_spec⟩

-- TODO: You get this theorem for free it you move these lemmas into/after Theorems/Equivalent.lean.
theorem obj?_some_iff (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    (∃ o, rtr₁[c][j] = some o) ↔ (∃ o, rtr₂[c][j] = some o) := by
  sorry

theorem obj?_none_iff (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    (rtr₁[c][j] = none) ↔ (rtr₂[c][j] = none) := by
  sorry

-- TODO: This is a general (perhaps very important) theorem about obj?.
theorem obj?_some_elim {rtr : α} {i : ID} (h : rtr[cpt][i] = some o) : (a.get? rtr cpt i = some o) ∨ (∃ j con, a.get? rtr .rtr j = some con ∧ con[cpt][i] = some o) :=
  sorry
  -- This should be derivable directly from obj?_to_con?_and_cpt?

-- TODO: It feels like basing obj? on an Object predicate instead of con? would make everything so much
--       nicer. In fact, Object would be so similar to Member, that perhaps we can merge the two.

theorem obj?_preserved (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) (h : c ≠ cpt ∨ j ≠ i) : 
    rtr₂[c][j] = rtr₁[c][j] := by
  cases ho₁ : rtr₁[c][j]
  case none => simp [u.obj?_none_iff.mp ho₁]
  case some =>
    have ⟨_, ho₂⟩ := u.obj?_some_iff.mp ⟨_, ho₁⟩ 
    simp [ho₂]

    -- TODO: We need to somehow distinguish whether [c][j] lives in the same reactor as [cpt][i].
    induction u
    case final e _ _ =>
      cases obj?_some_elim ho₁ <;> cases obj?_some_elim ho₂
      case inl.inl h₁ h₂ =>
        injection h₁ ▸ h₂ ▸ e (c := c) (j := j) (by simp [h]) with h
        exact h.symm
      case inr.inr h₁ h₂ =>
        obtain ⟨j₁, con₁, hn₁, hc₁⟩ := h₁
        obtain ⟨j₂, con₂, hn₂, hc₂⟩ := h₂
        simp at hc₁ hc₂
        have hj : j₁ = j₂ := sorry 
        subst hj
        have hn := e (c := .rtr) (j := j₁) (by simp [h])
        injection hn₂ ▸ hn ▸ hn₁ with h
        subst h
        injection hc₁ ▸ hc₂ with h
        exact h.symm
      case inl.inr =>
        simp at * -- contra
        sorry
      case inr.inl =>
        simp at * -- contra
        sorry
    case nest =>
      sorry

theorem obj?_updated (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : 
    rtr₂[cpt][i] = f <$> rtr₁[cpt][i] := by
  induction u
  case final h₁ h₂ => 
    rw [get?_some_to_obj?_some h₁, get?_some_to_obj?_some h₂, Option.map_some]
  case nest h₁ h₂ u hi =>
    have ⟨_, h₁'⟩ := u.obj?_some₁
    have ⟨_, h₂'⟩ := u.obj?_some₂
    rw [obj?_some_nested h₁ h₁', obj?_some_nested h₂ h₂']
    exact h₁' ▸ h₂' ▸ hi

end LawfulMemUpdate

namespace LawfulUpdate

open Indexable
variable [Indexable α] {rtr₁ : α}

theorem obj?_preserved (h : c ≠ cpt ∨ j ≠ i) : 
    (LawfulUpdate cpt i f rtr₁ rtr₂) → rtr₂[c][j] = rtr₁[c][j]
  | update u   => u.obj?_preserved h
  | notMem _ h => h ▸ rfl

theorem obj?_updated : (LawfulUpdate cpt i f rtr₁ rtr₂) → rtr₂[cpt][i] = f <$> rtr₁[cpt][i]
  | update u => u.obj?_updated
  | notMem h e => by subst e; simp [member_isEmpty_obj?_none h]

end LawfulUpdate
end ReactorType