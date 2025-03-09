import ReactorModel.Objects.Reactor.Proper
import ReactorModel.Objects.Reactor.Finite

open Reactor

namespace LoopModel

inductive Ident where
  | r
  | a

@[ext]
structure Rtr where
  act : Bool

instance : Identifiable Rtr where
  Id := Ident

instance : Valued Rtr where
  Val          := Bool
  value.absent := false

instance : Prioritizable Rtr where
  Priority := Unit
  order    := inferInstance

def Rtr.rcn : Reaction Rtr where
  deps _               := {⟨.act, .a⟩}
  triggers             := {⟨.act, .a⟩}
  prio                 := .unit
  body inp             := [.act .a inp.tag.time true]
  triggers_sub_in_deps := by simp_all
  target_mem_deps      := by simp_all [Change.Normal.target]

instance : Reactor Rtr where
  get? rtr
    | .rcn, .r => Rtr.rcn
    | .act, .a => rtr.act
    | _,    _  => none

instance : Extensional Rtr where
  ext_iff := by
    intro rtr₁ rtr₂
    constructor <;> intro h
    case mp  => rw [h]
    case mpr => ext; injection (by rw [h] : rtr₁{.act}{Ident.a} = rtr₂{.act}{Ident.a})

instance : Hierarchical Rtr where
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

instance : WellFounded Rtr where
  wf := by
    constructor; intro rtr₁
    constructor; intro rtr₂ h
    have ⟨_, _⟩ := h
    contradiction

instance : Updatable Rtr where
  update rtr
    | .act, .a, v => { act := v }
    | _,    _,  _ => rtr

instance : LawfulUpdatable Rtr where
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

instance : Proper Rtr where
  unique_ids     := Hierarchical.unique_ids
  wf             := WellFounded.wf
  update         := Updatable.update
  lawful         := LawfulUpdatable.lawful
  wellformed rtr := {
    unique_inputs h₁ h₂ hi :=
      -- Contradiction, we have two distinct ids which both map to `some` reaction.
      sorry
    ordered_prio _ h₁ h₂ hi :=
      -- Contradiction, we have two distinct ids which both map to `some` reaction.
      sorry
    valid_deps hn hr hd := sorry
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

example {p : A → Prop} (h : ∀ x, ¬p x) : {a | p a} = ∅ := by
  exact Set.subset_eq_empty h rfl

instance : Reactor.Finite Rtr where
  fin rtr cpt := by
    cases cpt <;> try cases ‹Component.Valued›
    case act =>
      simp only [Partial.Finite, Partial.ids]
      sorry -- This should hold because `Ident` is finite, so any set over `Ident` is finite.
    case rcn =>
      simp only [Partial.Finite, Partial.ids]
      sorry -- This should hold because `Ident` is finite, so any set over `Ident` is finite.
    case rtr =>
      simp only [Partial.Finite, Partial.ids]
      sorry -- The top level reactor is also counted.
    case' inp => have h : rtr[.inp].ids = ∅ := ?_
    case' out => have h : rtr[.out].ids = ∅ := ?_
    case' stv => have h : rtr[.stv].ids = ∅ := ?_
    all_goals
      first
        | simp only [Partial.Finite, h, Set.finite_empty]
        | apply Set.subset_eq_empty ?_ rfl
          intro i h
          simp [Partial.ids, Hierarchical.obj?] at h
          have ⟨_, ⟨_, _⟩, _⟩ := h
          cases ‹Object _ _ _ _›; cases ‹Member _ _ _›; cases ‹StrictMember _ _ _› <;> contradiction

end LoopModel
