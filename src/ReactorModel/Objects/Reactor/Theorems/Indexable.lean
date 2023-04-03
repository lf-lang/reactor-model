import ReactorModel.Objects.Reactor.Indexable

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
  case none.some => sorry
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

theorem obj?_preserved_id {c : Reactor.Component.Valued} (h : j ≠ i) : 
    (update rtr cpt i f)[c][j] = rtr[c][j] :=
  obj?_preserved $ .inr h

theorem obj?_updated {rtr : α} : (update rtr cpt i f)[cpt][i] = f <$> rtr[cpt][i] :=
  lawful rtr cpt i f |>.obj?_updated

end LawfulUpdatable
end ReactorType