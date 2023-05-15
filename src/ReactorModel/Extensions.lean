import Mathlib.Data.Finmap
import Mathlib.Data.Set.Finite

open Classical

class HasHEquiv (α : Sort u) (β : Sort v) where
  HEquiv : α → β → Sort w

infix:50 " ∼ "  => HasHEquiv.HEquiv

namespace List

instance : Coe (List α) (Set α) where
  coe l := { a : α | a ∈ l }

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

def ids (f : α ⇀ β) := { a | ∃ b, f a = some b }

instance : Membership α (α ⇀ β) where
  mem a f := a ∈ f.ids 

theorem mem_def {f : α ⇀ β} : (a ∈ f) ↔ (a ∈ f.ids) := by
  rfl

theorem mem_iff {f : α ⇀ β} : (a ∈ f) ↔ (∃ b, f a = some b) := by
  rfl

def empty : α ⇀ β :=  
  fun _ => none

instance {α β : Type _} : EmptyCollection (α ⇀ β) where
  emptyCollection := empty

theorem empty_iff {f : α ⇀ β} : (f = ∅) ↔ (∀ a, f a = none) where
  mp h _ := h ▸ rfl
  mpr h := funext h  

theorem empty_iff_ids_empty {f : α ⇀ β} : (f = ∅) ↔ (f.ids = ∅) := by
  simp [ids, empty_iff, Set.eq_empty_iff_forall_not_mem, Option.eq_none_iff_forall_not_mem]

theorem empty_ids : (∅ : α ⇀ β).ids = ∅ := 
  empty_iff_ids_empty.mp rfl

theorem not_mem_empty {a : α} : a ∉ (∅ : α ⇀ β) := by
  simp [mem_def, empty_ids]

def Nonempty (f : α ⇀ β) : Prop :=
  f ≠ ∅  

namespace Nonempty

theorem «def» {f : α ⇀ β} : f.Nonempty ↔ (f ≠ ∅) :=
  Iff.refl _ 

theorem not_to_empty {f : α ⇀ β} (h : ¬f.Nonempty) : f = ∅ :=
  byContradiction (Nonempty.def.not.mp h ·)

theorem iff_ids_nonempty {f : α ⇀ β} : f.Nonempty ↔ f.ids.Nonempty := by
  simp [Nonempty, Set.nonempty_iff_ne_empty, empty_iff_ids_empty]

theorem exists_mem {f : α ⇀ β} (n : f.Nonempty) : ∃ a, a ∈ f := by
  simp [iff_ids_nonempty, mem_def] at *
  exact ⟨_, n.some_mem⟩

end Nonempty

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
  funext a
  simp [map, Option.map, attach]
  split <;> split at * <;> simp_all
  case _ h => simp [←h]

def restrict (f : α ⇀ β) (s : Set α) [DecidablePred (· ∈ s)] : α ⇀ β := 
  fun a => if a ∈ s then f a else none 

theorem ext_restrict {f g : α ⇀ β} (h : ∀ a ∈ s, f a = g a) [DecidablePred (· ∈ s)] : 
    (f.restrict s) = (g.restrict s) := by
  simp [restrict]
  funext
  split <;> simp_all

def insert [DecidableEq α] (f : α ⇀ β) (a : α) (b : β) : α ⇀ β :=
  fun a' => if a' = a then b else f a'

theorem insert_same [DecidableEq α] (f : α ⇀ β) : (f.insert a b) a = b := by
  simp [insert]

theorem insert_ne [DecidableEq α] (f : α ⇀ β) (h : a' ≠ a := by assumption) : 
    (f.insert a b) a' = f a' := by
  simp [insert, h]

def update [DecidableEq α] (f : α ⇀ β) (a : α) (g : β → β) : α ⇀ β :=
  fun a' => if a' = a then g <$> f a else f a'

theorem update_ne_comm [DecidableEq α] (f : α ⇀ β) {a₁ a₂ : α} (h : a₁ ≠ a₂) (g₁ g₂ : β → β) :
    (f.update a₁ g₁).update a₂ g₂ = (f.update a₂ g₂).update a₁ g₁ := by
  ext1 a; by_cases a = a₁ <;> by_cases a = a₂ <;> simp_all [update]

def const (as : Set α) (b : β) [DecidablePred (· ∈ as)] : α ⇀ β :=
  fun a => if a ∈ as then b else none

theorem const_ids (as : Set α) (b : β) : (const as b).ids = as := by
  simp [const, ids]
  ext; simp; split <;> simpa

theorem const_eq_map_const (f : α ⇀ β) (b : b) : f.map (fun _ => b) = const f.ids b := by
  ext1 a
  simp [const, map_val, ids]
  split <;> simp [Option.map]
  case inl h => have ⟨_, h⟩ := h; simp [h]
  case inr h => 
    cases hb : f a <;> simp
    case some b => push_neg at h; have := hb ▸ h b; contradiction

def Finite (f : α ⇀ β) : Prop :=
  f.ids.Finite

end Partial

namespace Finmap

infix:50 " ⇉ " => (Finmap fun _ : · => ·)

instance [DecidableEq α] : CoeFun (α ⇉ β) (fun _ => α → Option β) where
  coe f := f.lookup

end Finmap