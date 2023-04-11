import ReactorModel.Objects.Reactor.Indexable
import ReactorModel.Objects.Reactor.Updatable
import ReactorModel.Objects.Reactor.Theorems.Basic

namespace ReactorType
namespace StrictMember

open Indexable
variable [Indexable α] {rtr rtr₁ : α}

theorem unique (s₁ s₂ : StrictMember cpt i rtr) : s₁ = s₂ := by
  injection unique_ids.allEq (.strict s₁) (.strict s₂)

theorem rtr_equiv 
    (e : rtr₁ ≈ rtr₂) (s₁ : StrictMember .rtr i rtr₁) (s₂ : StrictMember .rtr i rtr₂) : 
    s₁.object ≈ s₂.object := by
  induction s₁ generalizing rtr₂ <;> cases s₂
  case final.final h₁ _ h₂ => exact Equivalent.get?_rtr_some_equiv e h₁ h₂
  case nested.nested j₁ _ h₁ s₁ hi j₂ _ s₂ h₂ =>
    suffices hj : j₁ = j₂ by subst hj; exact hi (Equivalent.get?_rtr_some_equiv e h₁ h₂) _
    have hs := (nested h₁ s₁ |>.fromEquiv e).unique (nested h₂ s₂)
    simp [fromEquiv] at hs
    exact hs.left
  case final.nested h₁ _ _ s₂ h₂ => 
    injection (final h₁ |>.fromEquiv e).unique (nested h₂ s₂)
  case nested.final h₁ s₁ _ _ h₂ =>
    injection (nested h₁ s₁).unique (final h₂ |>.fromEquiv $ ReactorType.Equivalent.symm e) 

end StrictMember

/- ---------------------------------------------------------------------------------------------- -/
namespace Member

open Indexable
variable [Indexable α] {rtr rtr₁ : α}

theorem unique (m₁ m₂ : Member cpt i rtr) : m₁ = m₂ :=
  unique_ids.allEq m₁ m₂

theorem rtr_equiv (e : rtr₁ ≈ rtr₂) : 
    (m₁ : Member .rtr i rtr₁) → (m₂ : Member .rtr i rtr₂) →  m₁.object ≈ m₂.object
  | root,      root      => e
  | strict s₁, strict s₂ => s₁.rtr_equiv e s₂

end Member

/- ---------------------------------------------------------------------------------------------- -/
namespace Object

open Indexable
variable [Indexable α] {rtr : α}

theorem unique : (Object rtr cpt i o₁) → (Object rtr cpt i o₂) → o₁ = o₂
  | ⟨m₁⟩, ⟨m₂⟩ => m₁.unique m₂ ▸ rfl

theorem iff_obj?_some : (Object rtr cpt i o) ↔ (rtr[cpt][i] = some o) where
  mp := by 
    intro ⟨m⟩
    simp [obj?]
    split
    case inl h =>
      have ⟨m', h'⟩ := Object.def.mp h.choose_spec
      simp [←h', m.unique m']
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
      exact Option.some_inj.mp h ▸ h' ▸ ⟨m'⟩ 

theorem not_iff_obj?_none : (∀ o, ¬Object rtr cpt i o) ↔ (rtr[cpt][i] = none) := by
  simp [Option.eq_none_iff_forall_not_mem, iff_obj?_some]

end Object

/- ---------------------------------------------------------------------------------------------- -/
namespace Indexable

variable [Indexable α] {rtr : α}

theorem get?_some_to_obj?_some (h : get? rtr cpt i = some o) : rtr[cpt][i] = some o :=
  Object.iff_obj?_some.mp ⟨.final h⟩ 

theorem obj?_root_some (ho : rtr[.rtr][⊤] = some o) : o = rtr :=
  have ⟨m⟩ := Object.iff_obj?_some.mpr ho
  match m with | .root => rfl

-- Note: This theorem does not hold for `i' = ⊤`. For a version that supports this case see 
--       `obj?_some_nested'`.
theorem obj?_some_nested {i' : ID} (h : get? rtr .rtr i = some rtr') (ho : rtr'[cpt][i'] = some o) : 
    rtr[cpt][i'] = some o := by
  have ⟨s, hs⟩ := Object.strict_elim $ Object.iff_obj?_some.mpr ho
  exact Object.iff_obj?_some.mp $ hs ▸ ⟨.nested h s⟩ 

theorem obj?_some_nested' (h : get? rtr .rtr i = some rtr') (ho : rtr'[cpt][i'] = some o) : 
    ∃ j, rtr[cpt][j] = some o := by
  cases cpt <;> try cases i'
  case rtr.none =>
    exists i
    exact Object.iff_obj?_some.mp $ obj?_root_some ho ▸ ⟨.final h⟩ 
  all_goals 
    exact ⟨_, obj?_some_nested h ho⟩ 

theorem obj?_some_extend (ho : rtr[.rtr][c] = some con) (hc : get? con cpt i = some o) :
    rtr[cpt][i] = some o := by
  have ⟨m⟩ := Object.iff_obj?_some.mpr ho
  exact Object.iff_obj?_some.mp $ m.extend_object hc ▸ ⟨m.extend hc⟩

-- Note: This theorem does not hold for `i = ⊤`.
theorem obj?_some_split {i : ID} (ho : rtr[cpt][i] = some o) : 
    ∃ c con, (rtr[.rtr][c] = some con) ∧ (get? con cpt i = some o) := by
  have ⟨s, hs⟩ := Object.strict_elim $ Object.iff_obj?_some.mpr ho
  have ⟨c, ⟨m, hm⟩⟩ := s.split'
  exact ⟨c, m.object, Object.iff_obj?_some.mp ⟨m⟩, hs ▸ hm⟩

theorem member_isEmpty_obj?_none (h : IsEmpty $ Member cpt i rtr) : rtr[cpt][i] = none :=
  Object.not_iff_obj?_none.mp (Object.not_of_member_isEmpty h ·)

theorem get?_some_rtr_eq (ho₁ : rtr[.rtr][c₁] = some con₁) (ho₂ : rtr[.rtr][c₂] = some con₂) 
    (hc₁ : get? con₁ cpt j = some o₁) (hc₂ : get? con₂ cpt j = some o₂) : c₁ = c₂ := by
  have ⟨m₁⟩ := Object.iff_obj?_some.mpr ho₁
  have ⟨m₂⟩ := Object.iff_obj?_some.mpr ho₂
  exact Member.extend_inj $ (m₁.extend hc₁).unique (m₂.extend hc₂) 
    
theorem mem_get?_rtr_eq (ho₁ : rtr[.rtr][c₁] = some con₁) (ho₂ : rtr[.rtr][c₂] = some con₂) 
    (hc₁ : j ∈ get? con₁ cpt) (hc₂ : j ∈ get? con₂ cpt) : c₁ = c₂ :=
  get?_some_rtr_eq ho₁ ho₂ (Partial.mem_iff.mp hc₁).choose_spec (Partial.mem_iff.mp hc₂).choose_spec

end Indexable

namespace Equivalent

variable [Indexable α] {rtr₁ : α}

theorem obj?_rcn_eq (e : rtr₁ ≈ rtr₂) : rtr₁[.rcn] = rtr₂[.rcn] := by
  funext i
  cases ho : rtr₁[.rcn][i]
  case none =>
    apply Eq.symm
    apply Object.not_iff_obj?_none.mp
    intro o ob₂
    have := Object.not_iff_obj?_none.mpr ho o
    sorry -- I think we need to establish lemmas about Member witnesses for equivalent reactors and
          -- hence lemmas about Object for equivalent reactors.
  case some =>
    sorry

theorem obj?_rtr_equiv 
    (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][i] = some n₁) (h₂ : rtr₂[.rtr][i] = some n₂) : n₁ ≈ n₂ := by
  have ⟨m₁⟩ := Object.iff_obj?_some.mpr h₁
  have ⟨m₂⟩ := Object.iff_obj?_some.mpr h₂
  exact m₁.rtr_equiv e m₂

-- TODO: Generalize this to non-Indexable reactor types.
theorem obj?_some_iff (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, rtr₁[cpt][i] = some o₁) ↔ (∃ o₂, rtr₂[cpt][i] = some o₂) := by
  constructor
  all_goals
    intro ⟨_, h⟩
    have ⟨m⟩ := Object.iff_obj?_some.mpr h    
    refine ⟨_, Object.iff_obj?_some.mp ⟨m.fromEquiv ?_⟩⟩   
  case mp  => exact e
  case mpr => exact Equivalent.symm e

-- TODO: Generalize this to non-Indexable reactor types.
theorem mem_iff {i} (e : rtr₁ ≈ rtr₂) : (i ∈ rtr₁[cpt]) ↔ (i ∈ rtr₂[cpt]) := by
  simp [Partial.mem_iff, obj?_some_iff e]

end Equivalent

/- ---------------------------------------------------------------------------------------------- -/
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

/- ---------------------------------------------------------------------------------------------- -/
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