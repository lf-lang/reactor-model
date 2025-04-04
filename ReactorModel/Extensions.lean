import Mathlib.Data.Finmap
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Insert

open Classical

class HasHEquiv (α : Sort u) (β : Sort v) where
  HEquiv : α → β → Sort w

infix:50 " ∼ "  => HasHEquiv.HEquiv

namespace List

instance : Coe (List α) (Set α) where
  coe l := { a : α | a ∈ l }

end List

theorem Set.insert_union' (s₁ s₂ : Set α) (a : α) : (insert a s₁) ∪ s₂ = s₁ ∪ (insert a s₂) := by
  rw [Set.insert_union, Set.union_comm, ←Set.insert_union, Set.union_comm]

abbrev Partial (α β) := α → Option β

infixr:50 " ⇀ " => Partial

namespace Partial

def ids (f : α ⇀ β) := { a | ∃ b, f a = some b }

instance : Membership α (α ⇀ β) where
  mem f a := a ∈ f.ids

theorem mem_def {f : α ⇀ β} : (a ∈ f) ↔ (a ∈ f.ids) := by
  rfl

theorem mem_iff {f : α ⇀ β} : (a ∈ f) ↔ (∃ b, f a = some b) := by
  rfl

def empty : α ⇀ β :=
  fun _ => none

instance {α β : Type _} : EmptyCollection (α ⇀ β) where
  emptyCollection := empty

@[simp]
theorem apply_empty : (∅ : α ⇀ β) a = none := by
  rfl

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

@[simp]
theorem map_empty (g : β → γ) : Partial.map g (∅ : α ⇀ β) = ∅ :=
  rfl

theorem map_val (f : α ⇀ β) (g : β → γ) : (f.map g) a = (f a).map g :=
  rfl

theorem map_map (f : α ⇀ β) (g₁ : β → γ) (g₂ : γ → δ) : (f.map g₁).map g₂ = f.map (g₂ ∘ g₁) := by
  unfold map
  simp

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
  unfold restrict
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

@[simp]
theorem update_self (f : α ⇀ β) (a : α) (g : β → β) : (f.update a g) a = g <$> f a := by
  simp [update]

theorem update_ne_comm [DecidableEq α] (f : α ⇀ β) {a₁ a₂ : α} (h : a₁ ≠ a₂) (g₁ g₂ : β → β) :
    (f.update a₁ g₁).update a₂ g₂ = (f.update a₂ g₂).update a₁ g₁ := by
  ext1 a; by_cases a = a₁ <;> by_cases a = a₂ <;> simp_all [update]

def const (as : Set α) (b : β) [DecidablePred (· ∈ as)] : α ⇀ β :=
  fun a => if a ∈ as then b else none

theorem const_ids (as : Set α) (b : β) : (const as b).ids = as := by
  simp [const, ids]

theorem const_eq_map_const (f : α ⇀ β) (b : b) : f.map (fun _ => b) = const f.ids b := by
  ext1 a
  simp [const, map_val, ids]
  split <;> simp [Option.map]
  case isTrue h => have ⟨_, h⟩ := h; simp [h]
  case isFalse h =>
    cases hb : f a <;> simp
    case some b => push_neg at h; have := hb ▸ h b; contradiction

def mapIdx (g : α → β) (f : α ⇀ β) [DecidablePred (· ∈ f)] : α ⇀ β :=
  fun a => if a ∈ f then g a else none

theorem mapIdx_ids (g : α → β) (f : α ⇀ β) : (f.mapIdx g).ids = f.ids := by
  simp [mapIdx, mem_iff, ids]

def Finite (f : α ⇀ β) : Prop :=
  f.ids.Finite

end Partial

namespace Finmap

infix:50 " ⇉ " => (Finmap fun _ : · => ·)

instance [DecidableEq α] : CoeFun (α ⇉ β) (fun _ => α → Option β) where
  coe f := f.lookup

theorem insert_keys [DecidableEq α] (f : α ⇉ β) (a b) :
    (f.insert a b).keys = Insert.insert a f.keys := by
  ext
  simp [Finmap.mem_keys]

end Finmap

instance [fin : Finite α] : Finite (WithTop α) :=
  match fin with
  | .intro (n := n) equiv =>
    .intro (n := n + 1) {
      toFun
        | ⊤       => 0
        | (a : α) => (equiv a) + 1
      invFun
        | 0          => ⊤
        | ⟨x + 1, _⟩ => equiv.invFun ⟨x, by omega⟩
      left_inv
        | ⊤       => rfl
        | (a : α) => by
          simp only [Fin.coe_eq_castSucc, Fin.coeSucc_eq_succ, Equiv.invFun_as_coe]
          split
          · simp [Fin.succ] at *
          next h =>
            simp only [Fin.succ, Equiv.toFun_as_coe, Nat.succ_eq_add_one, Fin.mk.injEq,
                       add_left_inj, WithTop.coe_eq_coe] at h
            subst h
            simp
      right_inv
        | 0          => rfl
        | ⟨x + 1, isLt⟩ => by ext; simp_all [Fin.val_add]
    }
