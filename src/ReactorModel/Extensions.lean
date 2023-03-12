import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finmap
import Mathlib.Tactic.LibrarySearch

open Lean

syntax "case' " (Lean.binderIdent*),* " => " tacticSeq : tactic
macro_rules
  | `(tactic| case' $[$xs*],* => $tac) => do
    let tacs ← xs.mapM fun xs => `(tactic| case $(xs[0]!) $(xs[1:])* => $tac)
    `(tactic| ($[$tacs]*))

namespace List

theorem filterMap_nil_iff {l : List α} : (l.filterMap f = []) ↔ (l.All₂ (f · = none)) := by
  sorry

theorem filterMap_cons_split {l : List α} {f : α → Option β} (h : l.filterMap f = hd :: tl) : 
    ∃ l₁ a l₂, (l₁ ++ a :: l₂ = l) ∧ (l₁.All₂ (f · = none)) ∧ (f a = some hd) ∧ (l₂.filterMap f = tl) :=
  sorry

def lastSome? (f : α → Option β) : List α → Option β
  | []    => none
  | a::as => match lastSome? f as with
    | some b => some b
    | none   => f a

theorem lastSome?_empty_eq_none : [].lastSome? f = none := rfl

theorem lastSome?_eq_some_iff {l : List α} : 
  (∃ b, l.lastSome? f = some b) ↔ (∃ b a, a ∈ l ∧ (f a) = some b) := 
  sorry

theorem lastSome?_eq_some {l : List α} : 
  (l.lastSome? f = some b) → ∃ (i : Fin l.length), (f l[i] = some b) ∧ (∀ {j}, (j > i) → f l[j] = none) :=
  sorry

theorem lastSome?_eq_some_split {l : List α} : 
  (l.lastSome? f = some b) → ∃ l₁ a l₂, (l = l₁ ++ a :: l₂) ∧ (f a = some b) ∧ (l₂.All₂ (f · = none)) :=
  sorry

theorem lastSome?_eq_none {l : List α} : (l.lastSome? f = none) → l.All₂ (f · = none) :=
  sorry

theorem lastSome?_head : 
  ((hd::tl).lastSome? f = some b) → (tl.lastSome? f = none) → some b = f hd :=
  sorry

theorem lastSome?_tail : 
  ((hd::tl).lastSome? f = some b) → (tl.lastSome? f = some b') → b = b' :=
  sorry

-- Notes: 
-- * This definition doesn't work if `r` isn't transitive.
-- * In `cons` we don't require `r a₁ a₂` as `r` need not be a total order.
inductive Topo (r : α → α → Prop) [IsTrans _ r] : List α → Prop
  | nil : Topo r []
  | singleton : Topo r [a]
  | cons : ¬(r a₂ a₁) → Topo r (a₂ :: tl) → Topo r (a₁ :: a₂ :: tl)

end List

namespace Set 

theorem insert_union' (s₁ s₂ : Set α) (a : α) : (insert a s₁) ∪ s₂ = s₁ ∪ (insert a s₂) := by
  rw [Set.insert_union, Set.union_comm, ←Set.insert_union, Set.union_comm]

theorem ssubset_ne {s₁ s₂ : Set α} (h : s₁ ⊂ s₂) : s₁ ≠ s₂ :=
  ssubset_iff_subset_ne.mp h |>.right

end Set

abbrev Partial (α β) := α → Option β

infixr:50 " ⇀ " => Partial

namespace Partial

instance {α β : Type _} : EmptyCollection (α ⇀ β) where
  emptyCollection := (fun _ => none) 

def supp (f : α ⇀ β) := { a | ∃ b, f a = some b }

abbrev ids (f : α ⇀ β) := f.supp

theorem mem_ids_iff {f : α ⇀ β} : (i ∈ f.ids) ↔ (∃ b, f i = some b) := by
  simp [ids, supp]

def attach (f : α ⇀ β) : α ⇀ { b // ∃ a, f a = some b } := 
  fun a => 
    match h : f a with
    | none => none
    | some b => some ⟨b, ⟨_, h⟩⟩

def map (g : β → γ) (f : α ⇀ β) : α ⇀ γ := 
  fun a => g <$> f a

theorem map_val (f : α ⇀ β) (g : β → γ) : (f.map g) a = (f a).map g := 
  rfl

theorem map_map (f : α ⇀ β) (g₁ : β → γ) (g₂ : γ → δ) : (f.map g₁).map g₂ = f.map (g₂ ∘ g₁) := by
  simp [map]

theorem map_inj {f₁ f₂ : α ⇀ β} (hi : g.Injective) (h : f₁.map g = f₂.map g) : f₁ = f₂ := by
  funext a
  replace h : f₁.map g a = f₂.map g a := by simp [h]
  exact Option.map_injective hi h

theorem attach_map_val (f : α ⇀ β) : f.attach.map Subtype.val = f := by
  sorry

def restrict (f : α ⇀ β) (s : Set α) [DecidablePred (· ∈ s)] : α ⇀ β := 
  fun a => if a ∈ s then f a else none 

def filterMap (f : α ⇀ β) (g : β → Option γ) : α ⇀ γ := 
  fun a => f a >>= g

end Partial

namespace Finmap

infixr:50 " ⇉ " => (Finmap fun _ : · => ·)

instance [DecidableEq α] : CoeFun (α ⇉ β) (fun _ => α → Option β) where
  coe f := f.lookup

end Finmap