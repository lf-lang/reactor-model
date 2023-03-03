import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
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

end List

namespace Finset 

theorem ssubset_ne {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂) : s₁ ≠ s₂ := 
  ssubset_iff_subset_ne.mp h |>.right

end Finset

-- We need to use our own `Finmap` type based on `α → Option β`, as this is integral for the 
-- definition of `Raw.Reactor`.
structure Finmap (α β) where
  lookup : α → Option β 
  finite : { a | lookup a ≠ none }.Finite

namespace Finmap

variables {α β : Type _} [DecidableEq α] [DecidableEq β]  

infixr:50 " ⇉ " => Finmap

-- A coercion so that finmaps can be called directly as functions.
instance : CoeFun (α ⇉ β) (fun _ => α → Option β) where
  coe f := f.lookup

-- This allows us to use `∅` as notation for the empty finite map.
instance : EmptyCollection (α ⇉ β) where 
  emptyCollection := { lookup := (fun _ => none), finite := by simp }  

instance : Inhabited (Finmap α β) where
  default := ∅

@[ext]
theorem ext : {f₁ f₂ : α ⇉ β} → (h : ∀ a, f₁ a = f₂ a) → f₁ = f₂
  | mk .., mk .., h => by simp; funext a; exact h a

-- The (finite) set of inputs for which a given finmap has an associated value.
noncomputable def ids (f : α ⇉ β) : Finset α :=
  f.finite.toFinset

theorem mem_ids_iff {f : α ⇉ β} : i ∈ f.ids ↔ ∃ b, f i = some b := by
  sorry

-- The (finite) set of values for which there exist inputs that map to them.
noncomputable def values (f : α ⇉ β) : Finset β :=
  let description := { v : β | ∃ i, f i = v }
  let finite : description.Finite := by
    let s := f.ids.image f.lookup
    let t := { v | ∃ i, f i = some v }.image Option.some
    suffices h : t ⊆ ↑s from sorry -- Set.Finite.subset (Finset.finite_toSet s) h
    intro x h
    simp at *
    have ⟨b, ⟨a, ha⟩, hb⟩ := h
    exists a
    apply And.intro
    case left => sorry -- simp [ids_def, ha]
    case right => simp [ha, hb]
  finite.toFinset

theorem mem_values_iff {f : α ⇉ β} : v ∈ f.values ↔ (∃ i, f i = some v) := by
  simp [values, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

def update (f : α ⇉ β) (a : α) (b : β) : α ⇉ β := {
  lookup := Function.update f.lookup a b,
  finite := sorry
}

theorem update_self (f : α ⇉ β) (a : α) (b : β) : (f.update a b) a = b :=
  sorry

theorem update_ne (f : α ⇉ β) (h : a ≠ a') (b : β) : (f.update a b) a' = f a' :=
  sorry

def map (f : α ⇉ β) (g : β → γ) : α ⇉ γ := {
  lookup := fun a => (f a) >>= (some ∘ g),
  finite := by
    suffices h : { a | (fun i => (f i) >>= (some ∘ g)) a ≠ none } ⊆ ↑f.ids
      from Set.Finite.subset (Finset.finite_toSet _) h
    intro x h
    sorry
}

theorem map_mem_ids {f : α ⇉ β} : i ∈ (f.map g).ids ↔ i ∈ f.ids :=
  sorry

theorem map_def {f : α ⇉ β} (h : (f.map g) i = some v) : ∃ m, f i = some m ∧ g m = v :=
  sorry

noncomputable def map' (f : α ⇉ γ) (g : α → Option β) (h : g.Injective) : β ⇉ γ := {
  lookup := fun b => 
    if h : ∃ a ∈ f.ids, g a = b -- This is unique because of h.
    then f h.choose
    else none
  finite := sorry
}

theorem map'_def {f : α ⇉ γ} {g : α → Option β} {h} : (g a = some b) → (f.map' g h b = f a) :=
  sorry   

def attach (f : α ⇉ β) : α ⇉ { b // b ∈ f.values } := {
  lookup := fun a =>
    match h:(f a) with
    | none => none
    | some b => some ⟨b, (mem_values_iff.mpr ⟨a, h⟩)⟩,
  finite := sorry
}

theorem attach_mem_ids {f : α ⇉ β} {i} : i ∈ f.attach.ids ↔ i ∈ f.ids :=
  sorry

theorem attach_def {f : α ⇉ β} {i} {b : β} {hb} (h : f.attach i = some ⟨b, hb⟩) : f i = b :=
  sorry

-- The finmap that contains only those entries from `f`, whose identifiers
-- satisfy the given predicate `p`.
noncomputable def filter (f : α ⇉ β) (p : α → Prop) [DecidablePred p] : α ⇉ β := {
  lookup := fun a => if p a then f a else none,
  finite := sorry
}

-- The finmap that contains only those entries from `f`, whose values
-- satisfy the given predicate `p`.
noncomputable def filter' (f : α ⇉ β) (p : β → Prop) [DecidablePred p] : α ⇉ β := {
  lookup := (fun a => 
    match f a with
    | some b => if p b then b else none
    | none => none
  ),
  finite := sorry
}

variable {p : β → Prop} [DecidablePred p]

theorem filter'_mem {f : α ⇉ β} {i : α} {b : β} : 
  (f.filter' p) i = some b ↔ f i = b ∧ p b :=
  sorry

theorem filter'_mem_values {f : α ⇉ β} {b : β} : 
  b ∈ (f.filter' p).values ↔ ∃ i : α, f i = b ∧ p b :=
  sorry 

def filterMap (f : α ⇉ β) (g : β → Option γ) : α ⇉ γ := {
  lookup := fun a => (f a) >>= g,
  finite := sorry
}

theorem filterMap_congr {f₁ f₂ : α ⇉ β} : (f₁ a = f₂ a) → (f₁.filterMap g a = f₂.filterMap g a) :=
  sorry

-- The finmap that containts only those entries from `f`, whose identifiers
-- are in a given set `as`.
noncomputable def restrict (f : α ⇉ β) (as : Finset α) : α ⇉ β :=
  f.filter (fun a => a ∈ as)

theorem restrict_ext {f₁ f₂ : α ⇉ β} {as : Finset α} : 
  (∀ a ∈ as, f₁ a = f₂ a) → f₁.restrict as = f₂.restrict as := 
  sorry

structure Forall₂ (r : β → γ → Prop) (f₁ : α ⇉ β) (f₂ : α → Option γ) : Prop where
  eqIDs : ∀ a, a ∈ f₁.ids ↔ f₂ a ≠ none
  rel : ∀ {a} {b : β} {c : γ}, (f₁ a = b) → (f₂ a = c) → r b c

def union (f₁ f₂ : α ⇉ β) : α ⇉ β := {
  lookup := fun a => (f₁ a).elim (f₂ a) .some,
  finite := sorry
}

instance : Union (α ⇉ β) where 
  union := union

end Finmap