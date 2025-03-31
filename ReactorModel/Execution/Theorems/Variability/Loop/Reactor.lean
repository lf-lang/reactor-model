import ReactorModel.Objects.Reactor.Proper
import ReactorModel.Objects.Reactor.Finite
import ReactorModel.Objects.Reactor.Theorems.Hierarchical
import ReactorModel.Execution.Theorems.Dependency

open Reactor

namespace Loop

inductive Ident where
  | r
  | a

@[ext]
structure Reactor where
  act : Bool

instance : Identifiable Reactor where
  Id := Ident

instance : Valued Reactor where
  Val          := Bool
  value.absent := false

instance : Prioritizable Reactor where
  Priority := Unit
  order    := inferInstance

def rcn : Reaction Reactor where
  deps _               := {⟨.act, .a⟩}
  triggers             := {⟨.act, .a⟩}
  prio                 := .unit
  body inp             := [.act .a inp.tag.time true]
  triggers_sub_in_deps := by simp_all
  target_mem_deps      := by simp_all [Change.Normal.target]

instance : _root_.Reactor Reactor where
  get? rtr
    | .rcn, .r => rcn
    | .act, .a => rtr.act
    | _,    _  => none

instance : Extensional Reactor where
  ext_iff := by
    intro rtr₁ rtr₂
    constructor <;> intro h
    case mp  => rw [h]
    case mpr => ext; injection (by rw [h] : rtr₁{.act}{Ident.a} = rtr₂{.act}{Ident.a})

instance : Hierarchical Reactor where
  unique_ids := by
    intro rtr cpt i
    constructor
    intro m₁ m₂
    cases m₁
    case root => cases m₂; rfl
    case strict s =>
      cases cpt
      case rtr => cases s <;> contradiction
      all_goals
        cases m₂; cases s <;> cases ‹StrictMember ..› <;> try contradiction
        next h₁ _ h₂ => have h := h₁ ▸ h₂; injection h with h; subst h; rfl

@[simp]
theorem obj?_rcn_r (rtr : Reactor) : rtr[.rcn][Ident.r] = some rcn := by
  rw [Hierarchical.obj?]
  split
  case isTrue h =>
    have o := h.choose_spec
    obtain ⟨_, ho⟩ := h
    rw [o.unique ho]
    cases ho; cases ‹Member ..›; cases ‹StrictMember ..›
    all_goals simp only [get?] at ‹_ = some _›
    next _ h => injection h with h; subst h; rfl
    next _ h => contradiction
  case isFalse h =>
    push_neg at h
    exact h _ ⟨.strict (.final rfl)⟩ |>.elim

@[simp]
theorem obj?_rcn_a (rtr : Reactor) : rtr[.rcn][Ident.a] = none := by
  rw [Hierarchical.obj?]
  split <;> try rfl
  obtain ⟨_, ⟨m⟩⟩ := ‹∃ _, _›
  cases m; cases ‹StrictMember ..› <;> contradiction

@[simp]
theorem rcn_ids (rtr : Reactor) : rtr[.rcn].ids = {.r} := by
  simp only [Partial.ids, Set.eq_singleton_iff_unique_mem, Set.mem_setOf_eq, obj?_rcn_r,
    Option.some.injEq, exists_eq', forall_exists_index, true_and]
  intro i _ _
  cases i <;> simp at *

-- TODO: This is exactly the same proof as `Reactor.obj?_rcn_r`.
@[simp]
theorem obj?_act_a (rtr : Reactor) : rtr[.act][Ident.a] = some rtr.act := by
  rw [Hierarchical.obj?]
  split
  case isTrue h =>
    have o := h.choose_spec
    obtain ⟨_, ho⟩ := h
    rw [o.unique ho]
    cases ho; cases ‹Member ..›; cases ‹StrictMember ..›
    all_goals simp only [get?] at ‹_ = some _›
    next _ h => injection h with h; subst h; rfl
    next _ h => contradiction
  case isFalse h =>
    push_neg at h
    exact h _ ⟨.strict (.final rfl)⟩ |>.elim

-- TODO: This is exactly the same proof as `Reactor.obj?_rcn_a`.
@[simp]
theorem obj?_act_r (rtr : Reactor) : rtr[.act][Ident.r] = none := by
  rw [Hierarchical.obj?]
  split <;> try rfl
  obtain ⟨_, ⟨m⟩⟩ := ‹∃ _, _›
  cases m; cases ‹StrictMember ..› <;> contradiction

@[simp]
theorem obj?_val_not_act (rtr : Reactor) {cpt : Component.Valued} (h : cpt ≠ .act := by simp) :
    rtr[cpt][i] = none := by
  cases cpt
  case act => contradiction
  all_goals
    rw [Hierarchical.obj?]
    split
    case isFalse => rfl
    case isTrue h =>
      obtain ⟨_, ⟨m⟩⟩ := ‹∃ _, _›
      cases m; cases ‹StrictMember ..› <;> contradiction

@[simp]
theorem val_not_act_empty (rtr : Reactor) {cpt : Component.Valued} (h : cpt ≠ .act := by simp) :
    rtr[cpt] = ∅ := by
  ext
  simp [obj?_val_not_act _ h]

theorem no_deps (rtr : Reactor) (i₁ i₂ : Reactor✦) : i₁ ≮[rtr] i₂ := by
  intro h
  induction h <;> try contradiction
  next i₁ _ i₂ _ _ _ _ _ _ _ _ =>
    cases i₁ <;> cases i₂ <;> simp_all
  next i _ _ _ hc hr _ hm _ =>
    have h := Reactor.Hierarchical.obj?_some_extend hc hr
    cases i
    case a => simp at h
    case r =>
      simp only [obj?_rcn_r, Option.some_inj] at h
      simp only [Reaction.Mutates, Reaction.Normal, ←h, not_forall, Classical.not_imp] at hm
      obtain ⟨_, _, h, hn⟩ := hm
      simp only [rcn, List.mem_cons, List.not_mem_nil, or_false] at h
      exact (h ▸ hn) .intro

instance : WellFounded Reactor where
  wf := by
    constructor; intro rtr₁
    constructor; intro rtr₂ h
    have ⟨_, _⟩ := h
    contradiction

instance : Updatable Reactor where
  update rtr
    | .act, .a, v => { act := v }
    | _,    _,  _ => rtr

instance : LawfulUpdatable Reactor where
  lawful rtr cpt i v := by
    cases cpt <;> cases i
    case act.a =>
      apply LawfulUpdate.update <| LawfulMemUpdate.final ?_ rfl rfl
      intro cpt i h
      cases cpt <;> cases i <;> try rfl
      all_goals cases ‹Component.Valued› <;> try rfl
      cases h <;> contradiction
    all_goals
      apply LawfulUpdate.notMem ?_ rfl
      · constructor; intro m; cases m; cases ‹StrictMember _ _ _› <;> contradiction

instance : Proper Reactor where
  unique_ids     := Hierarchical.unique_ids
  wf             := WellFounded.wf
  update         := Updatable.update
  lawful         := LawfulUpdatable.lawful
  wellformed rtr := {
    unique_inputs  h₁ h₂ hi := by rename_i i₁ _ i₂ _ _; cases i₁ <;> cases i₂ <;> simp_all
    ordered_prio _ h₁ h₂ hi := by rename_i i₁ _ i₂ _ _; cases i₁ <;> cases i₂ <;> contradiction
    valid_deps hn hr hd := by
      rename_i j r k _
      cases j
      case a => contradiction
      case r =>
        simp only [get?, Option.some.injEq] at hr
        subst hr
        simp only [rcn, Set.mem_singleton_iff] at hd
        subst hd
        cases k
        all_goals
          constructor
          simp [get?, Partial.mem_iff]
  }

instance : Finite Ident :=
  .intro (n := 2) {
    toFun
      | .r => 0
      | .a => 1
    invFun
      | 0 => .r
      | 1 => .a
    left_inv
      | .r | .a => rfl
    right_inv
      | 0 | 1      => rfl
      | ⟨_ + 2, _⟩ => by contradiction
  }

instance : Reactor.Finite Reactor where
  fin rtr cpt := by
    cases cpt <;> try cases ‹Component.Valued›
    case act => simp only [Partial.Finite, Partial.ids, @Set.toFinite Ident]
    case rcn => simp only [Partial.Finite, Partial.ids, @Set.toFinite Ident]
    case rtr => simp only [Partial.Finite, Partial.ids, @Set.toFinite (WithTop Ident)]
    case' inp => have h : rtr[.inp].ids = ∅ := ?_
    case' out => have h : rtr[.out].ids = ∅ := ?_
    case' stv => have h : rtr[.stv].ids = ∅ := ?_
    all_goals
      first
        | simp only [Partial.Finite, h, Set.finite_empty]
        | exact Set.subset_eq_empty (by simp [Partial.ids]) rfl
