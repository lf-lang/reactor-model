import ReactorModel.Objects.Reactor.Hierarchical
import ReactorModel.Objects.Reactor.Updatable
import ReactorModel.Objects.Reactor.Theorems.Basic

namespace Reactor
namespace StrictMember

open Hierarchical
variable [Hierarchical α] {rtr rtr₁ : α}

theorem unique (s₁ s₂ : StrictMember cpt i rtr) : s₁ = s₂ := by
  injection unique_ids.allEq (.strict s₁) (.strict s₂)

theorem equiv
    (e : rtr₁ ≈ rtr₂) (s₁ : StrictMember cpt i rtr₁) (s₂ : StrictMember cpt i rtr₂) : s₁ ∼ s₂ := by
  induction s₁ generalizing rtr₂ <;> cases s₂
  case final.final => constructor
  case nested.nested rtr₁ j₁ _ h₁ s₁ hi j₂ _ s₂ h₂ =>
    suffices hj : j₁ = j₂ by
      subst hj
      exact Equivalent.nested h₁ h₂ <| hi (Equivalent.get?_rtr_some_equiv e h₁ h₂) s₂
    have hs := (nested h₁ s₁ |>.fromEquiv e).unique (nested h₂ s₂)
    simp [fromEquiv] at hs
    exact hs.left
  case final.nested h₁ _ _ s₂ h₂ =>
    have h := (final h₁ |>.fromEquiv e).unique (nested h₂ s₂)
    simp [fromEquiv] at h
  case nested.final h₁ s₁ _ _ h₂ =>
    have h := (nested h₁ s₁).unique (final h₂ |>.fromEquiv <| Reactor.Equivalent.symm e)
    simp [fromEquiv] at h

-- TODO: In all three of the following theorems, the `final.nested` and `nested.final` cases could
--       be removed if we figure out how to use the above `equiv` theorem. Induction on the
--       membership witness equivalence doesn't seem to work. Perhaps you need to prove a custom
--       induction principle for `StrictMember.Equivalent`. This would also remove the need to prove
--       things like `j₁ = j₂` in the `nested` case each time.
--
--       Note that both of the following theorems are almost identical. The only difference happens
--       in the "local" view of things in the `final.final` case. Perhaps there's a more general
--       theorem here for lifting local properties to global properties. Though since these
--       properties are tied to `Equivalent`, it might not be generalizable.

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
    have h := (final h₁ |>.fromEquiv e).unique (nested h₂ s₂)
    simp [fromEquiv] at h
  case nested.final h₁ s₁ _ _ h₂ =>
    have h := (nested h₁ s₁).unique (final h₂ |>.fromEquiv <| Reactor.Equivalent.symm e)
    simp [fromEquiv] at h

theorem equiv_rcn_eq
    (e : rtr₁ ≈ rtr₂) (s₁ : StrictMember .rcn i rtr₁) (s₂ : StrictMember .rcn i rtr₂) :
    s₁.object = s₂.object := by
  induction s₁ generalizing rtr₂ <;> cases s₂
  case final.final h₁ _ h₂ => exact Equivalent.get?_rcn_some_eq e h₁ h₂
  case nested.nested j₁ _ h₁ s₁ hi j₂ _ s₂ h₂ =>
    suffices hj : j₁ = j₂ by subst hj; exact hi (Equivalent.get?_rtr_some_equiv e h₁ h₂) _
    have hs := (nested h₁ s₁ |>.fromEquiv e).unique (nested h₂ s₂)
    simp [fromEquiv] at hs
    exact hs.left
  case final.nested h₁ _ _ s₂ h₂ =>
    have h := (final h₁ |>.fromEquiv e).unique (nested h₂ s₂)
    simp [fromEquiv] at h
  case nested.final h₁ s₁ _ _ h₂ =>
    have h := (nested h₁ s₁).unique (final h₂ |>.fromEquiv <| Reactor.Equivalent.symm e)
    simp [fromEquiv] at h

theorem lawfulMemUpdate_object_preserved
    (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) (h : c ≠ cpt ∨ j ≠ i) (s₁ : StrictMember c j rtr₁)
    (s₂ : StrictMember c j rtr₂) : s₁.object = s₂.object := by
  induction s₁ generalizing rtr₂ <;> cases s₂ <;> simp [object]
  case final.final h₁ _ h₂ =>
    cases u
    case final e => simp_all [e.valued h]
    case nested e => simp_all [e (c := c) (.inl <| by simp)]
  case nested.nested j₁ _ h₁ s₁ hi j₂ _ s₂ h₂ =>
    have hj : j₁ = j₂ := by
      have hs := (nested h₁ s₁ |>.fromEquiv u.equiv).unique (nested h₂ s₂)
      simp [fromEquiv] at hs
      exact hs.left
    subst hj
    cases u
    case final e =>
      cases h₂ ▸ (e (c := .rtr) (j := j₁) (.inl <| by simp)) ▸ h₁
      simp [s₁.unique s₂]
    case nested j' _ _ u _ _ e =>
      by_cases hj : j₁ = j'
      case neg =>
        cases h₂ ▸ (e (c := .rtr) (j := j₁) (.inr hj)) ▸ h₁
        simp [s₁.unique s₂]
      case pos =>
        simp_all [hj]
        exact hi (h₁ ▸ h₂ ▸ u) _
  case final.nested h₁ _ _ s₂ h₂ =>
    have h := (final h₁ |>.fromEquiv u.equiv).unique (nested h₂ s₂)
    simp [fromEquiv] at h
  case nested.final h₁ s₁ _ _ h₂ =>
    have h := (nested h₁ s₁).unique (final h₂ |>.fromEquiv <| Reactor.Equivalent.symm u.equiv)
    simp [fromEquiv] at h

end StrictMember

/- ---------------------------------------------------------------------------------------------- -/
namespace Member

open Hierarchical
variable [Hierarchical α] {rtr rtr₁ : α}

theorem unique (m₁ m₂ : Member cpt i rtr) : m₁ = m₂ :=
  unique_ids.allEq m₁ m₂

theorem rtr_equiv (e : rtr₁ ≈ rtr₂) :
    (m₁ : Member .rtr i rtr₁) → (m₂ : Member .rtr i rtr₂) → m₁.object ≈ m₂.object
  | root,      root      => e
  | strict s₁, strict s₂ => s₁.rtr_equiv e s₂

theorem equiv_rcn_eq (e : rtr₁ ≈ rtr₂) :
    (m₁ : Member .rcn i rtr₁) → (m₂ : Member .rcn i rtr₂) → m₁.object = m₂.object
  | strict s₁, strict s₂ => s₁.equiv_rcn_eq e s₂

theorem lawfulMemUpdate_object_preserved
    (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) (h : c ≠ cpt ∨ j ≠ i) :
    (m₁ : Member c j rtr₁) → (m₂ : Member c j rtr₂) → m₁.object = m₂.object
  | .strict s₁, .strict s₂ => s₁.lawfulMemUpdate_object_preserved u h s₂

end Member

/- ---------------------------------------------------------------------------------------------- -/
namespace Object

open Hierarchical
variable [Hierarchical α] {rtr : α}

theorem unique : (Object rtr cpt i o₁) → (Object rtr cpt i o₂) → o₁ = o₂
  | ⟨m₁⟩, ⟨m₂⟩ => m₁.unique m₂ ▸ rfl

theorem iff_obj?_some : (Object rtr cpt i o) ↔ (rtr[cpt][i] = some o) where
  mp := by
    intro ⟨m⟩
    simp only [obj?]
    split
    case isTrue h =>
      have ⟨m', h'⟩ := Object.def.mp h.choose_spec
      simp [←h', m.unique m']
    case isFalse h =>
      push_neg at h
      specialize h m.object
      simp [Object.def] at h
  mpr h := by
    simp only [obj?] at h
    split at h
    case isFalse => contradiction
    case isTrue h h' =>
      have ⟨m', h'⟩ := Object.def.mp h'.choose_spec
      exact Option.some_inj.mp h ▸ h' ▸ ⟨m'⟩

theorem not_iff_obj?_none : (∀ o, ¬Object rtr cpt i o) ↔ (rtr[cpt][i] = none) := by
  simp [Option.eq_none_iff_forall_not_mem, iff_obj?_some]

end Object

/- ---------------------------------------------------------------------------------------------- -/
namespace Hierarchical

variable [Hierarchical α] {rtr : α}

theorem get?_some_to_obj?_some (h : rtr{cpt}{i} = some o) : rtr[cpt][i] = some o :=
  Object.iff_obj?_some.mp ⟨.final h⟩

theorem obj?_root_some (ho : rtr[.rtr][⊤] = some o) : o = rtr :=
  have ⟨m⟩ := Object.iff_obj?_some.mpr ho
  match m with | .root => rfl

-- Note: This theorem does not hold for `i' = ⊤`. For a version that supports this case see
--       `obj?_some_nested'`.
theorem obj?_some_nested {i' : ID} (h : rtr{.rtr}{i} = some rtr') (ho : rtr'[cpt][i'] = some o) :
    rtr[cpt][i'] = some o := by
  have ⟨s, hs⟩ := Object.strict_elim <| Object.iff_obj?_some.mpr ho
  exact Object.iff_obj?_some.mp <| hs ▸ ⟨.nested h s⟩

theorem obj?_some_nested' (h : rtr{.rtr}{i} = some rtr') (ho : rtr'[cpt][i'] = some o) :
    ∃ j, rtr[cpt][j] = some o := by
  cases cpt <;> try cases i'
  case rtr.none =>
    exists i
    exact Object.iff_obj?_some.mp <| obj?_root_some ho ▸ ⟨.final h⟩
  all_goals
    exact ⟨_, obj?_some_nested h ho⟩

theorem obj?_some_extend (ho : rtr[.rtr][c] = some con) (hc : con{cpt}{i} = some o) :
    rtr[cpt][i] = some o := by
  have ⟨m⟩ := Object.iff_obj?_some.mpr ho
  exact Object.iff_obj?_some.mp <| m.extend_object hc ▸ ⟨m.extend hc⟩

-- Note: This theorem does not hold for `i = ⊤`.
theorem obj?_some_split {i : ID} (ho : rtr[cpt][i] = some o) :
    ∃ c con, (rtr[.rtr][c] = some con) ∧ (con{cpt}{i} = some o) := by
  have ⟨s, hs⟩ := Object.strict_elim <| Object.iff_obj?_some.mpr ho
  have ⟨c, ⟨m, hm⟩⟩ := s.split'
  exact ⟨c, m.object, Object.iff_obj?_some.mp ⟨m⟩, hs ▸ hm⟩

theorem member_isEmpty_obj?_none (h : IsEmpty <| Member cpt i rtr) : rtr[cpt][i] = none :=
  Object.not_iff_obj?_none.mp (Object.not_of_member_isEmpty h ·)

theorem get?_some_rtr_eq (ho₁ : rtr[.rtr][c₁] = some con₁) (ho₂ : rtr[.rtr][c₂] = some con₂)
    (hc₁ : con₁{cpt}{j} = some o₁) (hc₂ : con₂{cpt}{j} = some o₂) : c₁ = c₂ := by
  have ⟨m₁⟩ := Object.iff_obj?_some.mpr ho₁
  have ⟨m₂⟩ := Object.iff_obj?_some.mpr ho₂
  exact Member.extend_inj <| (m₁.extend hc₁).unique (m₂.extend hc₂)

theorem mem_get?_rtr_eq (ho₁ : rtr[.rtr][c₁] = some con₁) (ho₂ : rtr[.rtr][c₂] = some con₂)
    (hc₁ : j ∈ con₁{cpt}) (hc₂ : j ∈ con₂{cpt}) : c₁ = c₂ :=
  get?_some_rtr_eq ho₁ ho₂ (Partial.mem_iff.mp hc₁).choose_spec (Partial.mem_iff.mp hc₂).choose_spec

theorem obj?_none_to_get?_none {i : ID} (ho : rtr[cpt][i] = none) : rtr{cpt}{i} = none := by
  replace ho := Object.not_iff_obj?_none.mpr ho
  by_contra h
  exact ho _ ⟨.final <| Option.ne_none_iff_exists.mp h |>.choose_spec.symm⟩

end Hierarchical

/- ---------------------------------------------------------------------------------------------- -/
namespace Equivalent

variable [Hierarchical α] {rtr₁ : α}

theorem obj?_some_iff (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, rtr₁[cpt][i] = some o₁) ↔ (∃ o₂, rtr₂[cpt][i] = some o₂) := by
  simp [←Object.iff_obj?_some, Object.equiv_exists_object_iff e]

theorem mem_iff {i} (e : rtr₁ ≈ rtr₂) : (i ∈ rtr₁[cpt]) ↔ (i ∈ rtr₂[cpt]) := by
  simp [Partial.mem_iff, obj?_some_iff e]

theorem ids_eq (e : rtr₁ ≈ rtr₂) : rtr₁[cpt].ids = rtr₂[cpt].ids := by
  ext1
  exact mem_iff e

theorem obj?_none_iff (e : rtr₁ ≈ rtr₂) : (rtr₁[cpt][i] = none) ↔ (rtr₂[cpt][i] = none) := by
  simp [←Object.not_iff_obj?_none]
  constructor
  all_goals
    intro h o ⟨m⟩
    refine h _ ⟨m.fromEquiv ?_⟩
  · exact Equivalent.symm e
  · exact e

theorem obj?_rtr_equiv
    (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][i] = some n₁) (h₂ : rtr₂[.rtr][i] = some n₂) : n₁ ≈ n₂ := by
  have ⟨m₁⟩ := Object.iff_obj?_some.mpr h₁
  have ⟨m₂⟩ := Object.iff_obj?_some.mpr h₂
  exact m₁.rtr_equiv e m₂

theorem obj?_rtr_equiv' (e : rtr₁ ≈ rtr₂) (h₂ : rtr₂[.rtr][i] = some n₂) :
    ∃ n₁, (rtr₁[.rtr][i] = some n₁) ∧ (n₁ ≈ n₂) := by
  have ⟨_, h₁⟩ := obj?_some_iff e |>.mpr ⟨_, h₂⟩
  exact ⟨_, h₁, Equivalent.obj?_rtr_equiv e h₁ h₂⟩

theorem obj?_rcn_eq (e : rtr₁ ≈ rtr₂) : rtr₁[.rcn] = rtr₂[.rcn] := by
  funext i
  cases ho₁ : rtr₁[.rcn][i]
  case none => simp [obj?_none_iff e |>.mp ho₁]
  case some =>
    have ⟨_, ho₂⟩ := obj?_some_iff e |>.mp ⟨_, ho₁⟩
    have ⟨m₁⟩ := Object.iff_obj?_some.mpr ho₁
    have ⟨m₂⟩ := Object.iff_obj?_some.mpr ho₂
    simp [ho₂, m₁.equiv_rcn_eq e m₂]

end Equivalent

/- ---------------------------------------------------------------------------------------------- -/
namespace LawfulMemUpdate

open Hierarchical
variable [Hierarchical α] {rtr₁ : α}

theorem obj?_some₁ (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) : ∃ o, rtr₁[cpt][i] = some o := by
  induction u
  case final           => exact ⟨_, get?_some_to_obj?_some ‹_›⟩
  case nested h _ _ hi => exact ⟨_, obj?_some_nested h hi.choose_spec⟩

theorem obj?_some₂ (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) : ∃ o, rtr₂[cpt][i] = some o := by
  induction u
  case final         => exact ⟨_, get?_some_to_obj?_some ‹_›⟩
  case nested h _ hi => exact ⟨_, obj?_some_nested h hi.choose_spec⟩

theorem obj?_some_iff (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) :
    (∃ o, rtr₁[c][j] = some o) ↔ (∃ o, rtr₂[c][j] = some o) :=
  Equivalent.obj?_some_iff u.equiv

theorem obj?_none_iff (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) :
    (rtr₁[c][j] = none) ↔ (rtr₂[c][j] = none) :=
  Equivalent.obj?_none_iff u.equiv

theorem obj?_preserved (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) (h : c ≠ cpt ∨ j ≠ i) :
    rtr₂[c][j] = rtr₁[c][j] := by
  cases ho₁ : rtr₁[c][j]
  case none => simp [obj?_none_iff u |>.mp ho₁]
  case some =>
    have ⟨_, ho₂⟩ := obj?_some_iff u |>.mp ⟨_, ho₁⟩
    have ⟨m₁⟩ := Object.iff_obj?_some.mpr ho₁
    have ⟨m₂⟩ := Object.iff_obj?_some.mpr ho₂
    simp [ho₂, m₁.lawfulMemUpdate_object_preserved u h m₂]

theorem obj?_updated (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) :
    rtr₂[cpt][i] = (fun _ => v) <$> rtr₁[cpt][i] := by
  induction u
  case final h₁ h₂ =>
    rw [get?_some_to_obj?_some h₁, get?_some_to_obj?_some h₂, Option.map_some]
  case nested h₁ h₂ u hi =>
    have ⟨_, h₁'⟩ := u.obj?_some₁
    have ⟨_, h₂'⟩ := u.obj?_some₂
    rw [obj?_some_nested h₁ h₁', obj?_some_nested h₂ h₂']
    exact h₁' ▸ h₂' ▸ hi

end LawfulMemUpdate

/- ---------------------------------------------------------------------------------------------- -/
namespace LawfulUpdate

open Hierarchical
variable [Hierarchical α] {rtr₁ : α}

theorem obj?_preserved (h : c ≠ cpt ∨ j ≠ i) :
    (LawfulUpdate cpt i v rtr₁ rtr₂) → rtr₂[c][j] = rtr₁[c][j]
  | update u   => u.obj?_preserved h
  | notMem _ h => h ▸ rfl

theorem obj?_updated :
    (LawfulUpdate cpt i v rtr₁ rtr₂) → rtr₂[cpt][i] = (fun _ => v) <$> rtr₁[cpt][i]
  | update u   => u.obj?_updated
  | notMem h e => by subst e; simp [member_isEmpty_obj?_none h]

end LawfulUpdate
end Reactor
