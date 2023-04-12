import ReactorModel.Objects.Reactor.Indexable
import ReactorModel.Objects.Reactor.Updatable
import ReactorModel.Objects.Reactor.Theorems.Basic

namespace ReactorType
namespace StrictMember

open Indexable
variable [Indexable α] {rtr rtr₁ : α}

theorem unique (s₁ s₂ : StrictMember cpt i rtr) : s₁ = s₂ := by
  injection unique_ids.allEq (.strict s₁) (.strict s₂)

-- TODO: In both of the following theorems, the `final.nested` and `nested.final` cases could be 
--       removed if we have a theorem that establishes that for indexable reactor types, if two
--       reactors are equivalent, then so are their membership witnesses.

-- TODO: Note that both of the following theorems are almost identical. The only difference happens
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
    injection (final h₁ |>.fromEquiv e).unique (nested h₂ s₂)
  case nested.final h₁ s₁ _ _ h₂ =>
    injection (nested h₁ s₁).unique (final h₂ |>.fromEquiv $ ReactorType.Equivalent.symm e) 

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
    (m₁ : Member .rtr i rtr₁) → (m₂ : Member .rtr i rtr₂) → m₁.object ≈ m₂.object
  | root,      root      => e
  | strict s₁, strict s₂ => s₁.rtr_equiv e s₂

theorem equiv_rcn_eq (e : rtr₁ ≈ rtr₂) :
    (m₁ : Member .rcn i rtr₁) → (m₂ : Member .rcn i rtr₂) → m₁.object = m₂.object 
  | strict s₁, strict s₂ => s₁.equiv_rcn_eq e s₂

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

theorem get?_some_to_obj?_some (h : rtr{cpt}{i} = some o) : rtr[cpt][i] = some o :=
  Object.iff_obj?_some.mp ⟨.final h⟩ 

theorem obj?_root_some (ho : rtr[.rtr][⊤] = some o) : o = rtr :=
  have ⟨m⟩ := Object.iff_obj?_some.mpr ho
  match m with | .root => rfl

-- Note: This theorem does not hold for `i' = ⊤`. For a version that supports this case see 
--       `obj?_some_nested'`.
theorem obj?_some_nested {i' : ID} (h : rtr{.rtr}{i} = some rtr') (ho : rtr'[cpt][i'] = some o) : 
    rtr[cpt][i'] = some o := by
  have ⟨s, hs⟩ := Object.strict_elim $ Object.iff_obj?_some.mpr ho
  exact Object.iff_obj?_some.mp $ hs ▸ ⟨.nested h s⟩ 

theorem obj?_some_nested' (h : rtr{.rtr}{i} = some rtr') (ho : rtr'[cpt][i'] = some o) : 
    ∃ j, rtr[cpt][j] = some o := by
  cases cpt <;> try cases i'
  case rtr.none =>
    exists i
    exact Object.iff_obj?_some.mp $ obj?_root_some ho ▸ ⟨.final h⟩ 
  all_goals 
    exact ⟨_, obj?_some_nested h ho⟩ 

theorem obj?_some_extend (ho : rtr[.rtr][c] = some con) (hc : con{cpt}{i} = some o) :
    rtr[cpt][i] = some o := by
  have ⟨m⟩ := Object.iff_obj?_some.mpr ho
  exact Object.iff_obj?_some.mp $ m.extend_object hc ▸ ⟨m.extend hc⟩

-- Note: This theorem does not hold for `i = ⊤`.
theorem obj?_some_split {i : ID} (ho : rtr[cpt][i] = some o) : 
    ∃ c con, (rtr[.rtr][c] = some con) ∧ (con{cpt}{i} = some o) := by
  have ⟨s, hs⟩ := Object.strict_elim $ Object.iff_obj?_some.mpr ho
  have ⟨c, ⟨m, hm⟩⟩ := s.split'
  exact ⟨c, m.object, Object.iff_obj?_some.mp ⟨m⟩, hs ▸ hm⟩

theorem member_isEmpty_obj?_none (h : IsEmpty $ Member cpt i rtr) : rtr[cpt][i] = none :=
  Object.not_iff_obj?_none.mp (Object.not_of_member_isEmpty h ·)

theorem get?_some_rtr_eq (ho₁ : rtr[.rtr][c₁] = some con₁) (ho₂ : rtr[.rtr][c₂] = some con₂) 
    (hc₁ : con₁{cpt}{j} = some o₁) (hc₂ : con₂{cpt}{j} = some o₂) : c₁ = c₂ := by
  have ⟨m₁⟩ := Object.iff_obj?_some.mpr ho₁
  have ⟨m₂⟩ := Object.iff_obj?_some.mpr ho₂
  exact Member.extend_inj $ (m₁.extend hc₁).unique (m₂.extend hc₂) 
    
theorem mem_get?_rtr_eq (ho₁ : rtr[.rtr][c₁] = some con₁) (ho₂ : rtr[.rtr][c₂] = some con₂) 
    (hc₁ : j ∈ con₁{cpt}) (hc₂ : j ∈ con₂{cpt}) : c₁ = c₂ :=
  get?_some_rtr_eq ho₁ ho₂ (Partial.mem_iff.mp hc₁).choose_spec (Partial.mem_iff.mp hc₂).choose_spec

theorem obj?_none_to_get?_none {i : ID} (ho : rtr[cpt][i] = none) : rtr{cpt}{i} = none := by
  replace ho := Object.not_iff_obj?_none.mpr ho
  by_contra h
  exact ho _ ⟨.final $ Option.ne_none_iff_exists.mp h |>.choose_spec.symm⟩ 

end Indexable

namespace Equivalent

variable [Indexable α] {rtr₁ : α}

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

-- TODO: Generalize this to non-Indexable reactor types.
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
end ReactorType