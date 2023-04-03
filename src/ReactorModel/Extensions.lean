import Mathlib.Data.Finmap

namespace Set 

theorem insert_union' (s₁ s₂ : Set α) (a : α) : (insert a s₁) ∪ s₂ = s₁ ∪ (insert a s₂) := by
  rw [Set.insert_union, Set.union_comm, ←Set.insert_union, Set.union_comm]

theorem ssubset_ne {s₁ s₂ : Set α} (h : s₁ ⊂ s₂) : s₁ ≠ s₂ :=
  ssubset_iff_subset_ne.mp h |>.right

end Set

abbrev Partial (α β) := α → Option β

infixr:50 " ⇀ " => Partial

namespace Partial

def empty : α ⇀ β :=  
  fun _ => none

instance {α β : Type _} : EmptyCollection (α ⇀ β) where
  emptyCollection := empty

theorem empty_iff {f : α ⇀ β} : (f = ∅) ↔ (∀ a, f a = none) where
  mp h _ := h ▸ rfl
  mpr h := funext h  
  
def Nonempty (f : α ⇀ β) : Prop :=
  f ≠ ∅  

def ids (f : α ⇀ β) := { a | ∃ b, f a = some b }

theorem empty_iff_ids_empty {f : α ⇀ β} : (f = ∅) ↔ (f.ids = ∅) := by
  simp [ids, empty_iff, Set.eq_empty_iff_forall_not_mem, Option.eq_none_iff_forall_not_mem]

theorem Nonempty.def {f : α ⇀ β} : f.Nonempty ↔ (f ≠ ∅) :=
  Iff.refl _ 

theorem Nonempty.iff_ids_nonempty {f : α ⇀ β} : f.Nonempty ↔ f.ids.Nonempty := by
  simp [Nonempty, Set.nonempty_iff_ne_empty, empty_iff_ids_empty]

instance : Membership α (α ⇀ β) where
  mem a f := a ∈ f.ids 

theorem mem_def {f : α ⇀ β} : (a ∈ f) ↔ (a ∈ f.ids) := by
  rfl

theorem mem_iff {f : α ⇀ β} : (a ∈ f) ↔ (∃ b, f a = some b) := by
  rfl

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

end Partial

namespace Finmap

instance [DecidableEq α] : CoeFun (Finmap fun _ : α => β) (fun _ => α → Option β) where
  coe f := f.lookup

end Finmap