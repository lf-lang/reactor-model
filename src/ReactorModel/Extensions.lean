import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finmap
import Mathlib.Data.List.Card

open Classical

syntax "case' " (Lean.binderIdent*),* " => " tacticSeq : tactic
macro_rules
  | `(tactic| case' $[$xs*],* => $tac) => do
    let tacs ← xs.mapM fun xs => `(tactic| case $(xs[0]!) $(xs[1:])* => $tac)
    `(tactic| ($[$tacs]*))

namespace List

def Topo (l : List α) (r : α → α → Prop) : Prop :=
  ∀ {i₁ i₂ : Nat} {a₁ a₂}, (l.get? i₁ = some a₁) → (l.get? i₂ = some a₂) → (r a₁ a₂) → i₁ < i₂ 

namespace Topo

theorem Topo.tail (t : Topo (hd :: tl) r) : Topo tl r :=
  sorry

theorem Topo.erase {l : List α} (t : Topo l r) (a : α) : Topo (l.remove a) r :=
  sorry

theorem Topo.head_indep (t : Topo (hd :: tl) r) : ∀ a ∈ tl, ¬(r a hd)  :=
  sorry

theorem Topo.move_indep {l : List α} (t : Topo l r) (ha : a ∈ l) (hi : ∀ b ∈ l, ¬(r b a)) : 
    Topo (a :: l.erase a) r :=
  sorry

end Topo
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

theorem ids_empty_iff {f : α ⇀ β} : (f.ids = ∅) ↔ (∀ i, f i = none) := by
  sorry

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

def insert [DecidableEq α] (f : α ⇀ β) (a : α) (b : β) : α ⇀ β :=
  fun a' => if a' = a then b else f a'

theorem insert_same [DecidableEq α] (f : α ⇀ β) : (f.insert a b) a = b := by
  simp [insert]

theorem insert_ne [DecidableEq α] (f : α ⇀ β) (h : a' ≠ a := by assumption) : 
    (f.insert a b) a' = f a' := by
  simp [insert, h]

end Partial

namespace Finmap

infixr:50 " ⇉ " => (Finmap fun _ : · => ·)

instance [DecidableEq α] : CoeFun (α ⇉ β) (fun _ => α → Option β) where
  coe f := f.lookup

end Finmap