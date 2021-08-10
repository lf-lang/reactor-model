import ReactorModel.Mathlib.Alist
import ReactorModel.Mathlib.Set
import ReactorModel.Mathlib.Option

structure Finmap {α : Type u} (β : α → Type v) : Type (max u v) where
  entries : Multiset (Sigma β)
  nodupkeys : entries.nodupkeys

def Alist.toFinmap [DecidableEq α] {β : α → Type _} (s : Alist β) : Finmap β := sorry

namespace Finmap

def liftOn [DecidableEq α] {β : α → Type v} {γ} (s : Finmap β) (f : Alist β → γ) (H : ∀ a b : Alist β, a.entries ~ b.entries → f a = f b) : γ := sorry

def lookup [DecidableEq α] {β : α → Type _} (a : α) (s : Finmap β) : Option (β a) := liftOn s (Alist.lookup a) (λ s t => Alist.permLookup)

theorem inductionOn [DecidableEq α] {β : α → Type _} {C : Finmap β → Prop} (s : Finmap β) (H : ∀ (a : Alist β), C a.toFinmap) : C s := sorry

def keys [DecidableEq α] {β : α → Type _} (s : Finmap β) : Finset α :=
  ⟨s.entries.keys, sorry⟩

instance [DecidableEq α] {β : α → Type _} : Mem α (Finmap β) := ⟨λ a s => a ∈ s.entries.keys⟩

theorem mem_keys [DecidableEq α] {a : α} {s : Finmap β} : a ∈ s.keys ↔ a ∈ s := sorry

theorem mem_def [DecidableEq α] {β : α → Type _} {a : α} {s : Finmap β} : a ∈ s ↔ a ∈ s.entries.keys := sorry

lemma mem_of_lookup_eq_some [DecidableEq α] {a : α} {b : β a} {s : Finmap β} (h : s.lookup a = some b) : a ∈ s := sorry

infix:50 " ⇀ " => (λ a b => Finmap (λ _ : a => b))

def ids [DecidableEq α] (f : α ⇀ β) := f.keys

noncomputable def values [DecidableEq α] [DecidableEq β] (f : α ⇀ β) : Finset β :=
  let description := { x | ∃ i ∈ f.keys, f.lookup i = some x }
  let isFinite : description.finite := by
    let s : Finset β := f.keys.bUnion (λ i => (f.lookup i).elim ∅ Finset.singleton)
    sorry
    /-suffices h : ↑s = description by simp only [←h, Finset.finite_to_set]  
    split
    focus 
      intro h
      simp only [finset.set_bUnion_coe, set.mem_Union, finset.coe_bUnion] at h
      match h with 
      | ⟨i, ⟨hi, hm⟩⟩ =>
        simp only [set.mem_set_of_eq]
        exists i
        exists hi
        cases f.lookup i
        allGoals simp only [option.elim] at hm
        focus
          exfalso
          simp only [finset.coe_empty, set.mem_empty_eq] at hm
          exact hm
        focus
          simp only [set.mem_singleton_iff, finset.coe_singleton] at hm
          simp only [hm]
    focus
      intro h
      simp only [set.mem_set_of_eq] at h
      match h with 
      | ⟨i, ⟨hi, he⟩⟩ =>
      simp only [finset.set_bUnion_coe, set.mem_Union, finset.coe_bUnion]
      exists i
      exists hi
      cases f.lookup i
      allGoals simp only [option.elim]
      allGoals simp only at he
      focus 
        exfalso
        exact he
      focus
        simp only [he, set.mem_singleton_iff, finset.coe_singleton]
    -/
  isFinite.toFinset

end Finmap