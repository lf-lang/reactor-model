import Mathlib

namespace List

def empty : List α → Bool
  | []       => true
  | (_ :: _) => false

def findIndex (p : α → Prop) [DecidablePred p] : List α → Nat
  | []     => 0
  | (a::l) => if p a then 0 else Nat.succ (findIndex p l)

theorem index_of_cons_self [DecidableEq α] (a : α) (l : List α) : 
  indexOf a (a::l) = 0 := 
  sorry

variable (r : α → α → Prop)

theorem pairwisePWFilter {R : α → α → Prop} [DecidableRel R] : 
  ∀ (l : List α), Pairwise R (pwFilter R l) := 
  sorry

def sorted : List α → Prop := Pairwise r

theorem nodup_erase_of_nodup [DecidableEq α] (a : α) {l} : 
  Nodup l → Nodup (l.erase a) := 
  sorry

-- From the old "mathlib.lean"
theorem index_of_erase_lt {α : Type _} [DecidableEq α] {l : List α} {e x x' : α} (h : l.indexOf x < l.indexOf x') (hₘ : x ∈ l.erase e) (hₘ' : x' ∈ l.erase e) (hₙ : Nodup l) :
  (l.erase e).indexOf x < (l.erase e).indexOf x' := 
  sorry

theorem nodupEraseDup [DecidableEq α] : ∀ l : List α, Nodup l.eraseDup := pairwisePWFilter

theorem perm_ext {l₁ l₂ : List α} (d₁ : Nodup l₁) (d₂ : Nodup l₂) : 
  l₁ ~ l₂ ↔ ∀a, a ∈ l₁ ↔ a ∈ l₂ := 
  sorry

theorem perm.mem_iff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : 
  a ∈ l₁ ↔ a ∈ l₂ :=
  sorry

theorem Perm.length_eq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ h => simp [h]
  | swap => simp
  | trans _ _ h₁ h₂ => exact Eq.trans h₁ h₂

theorem Perm.eq_nil {l : List α} (p : l ~ []) : 
  l = [] := 
  eq_nil_of_length_eq_zero p.length_eq

theorem Perm.nil_eq {l : List α} (p : [] ~ l) : 
  [] = l := 
  p.symm.eq_nil.symm

theorem Perm.cons_inv {a : α} {l₁ l₂ : List α} : a::l₁ ~ a::l₂ → l₁ ~ l₂ := sorry

theorem Perm.pairwise_iff {R : α → α → Prop} (S : ∀ {x y}, R x y → R y x) : ∀ {l₁ l₂ : List α} (p : l₁ ~ l₂), Pairwise R l₁ ↔ Pairwise R l₂ := sorry

theorem Perm.nodup_iff {l₁ l₂ : List α} : l₁ ~ l₂ → (Nodup l₁ ↔ Nodup l₂) := Perm.pairwise_iff Ne.symm

theorem Perm.mem_iff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ := sorry

def keys {β : α → Type v} : List (Sigma β) → List α := map Sigma.fst

def nodupkeys {β : α → Type v} (l : List (Sigma β)) : Prop := Nodup l.keys

theorem filterMapConsSome (f : α → Option β) (a : α) (l : List α) {b : β} (h : f a = some b) : filterMap f (a :: l) = b :: filterMap f l := sorry

theorem filterMapEqMap (f : α → β) : filterMap (some ∘ f) = map f := sorry

theorem Perm.filterMap (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : filterMap f l₁ ~ filterMap f l₂ := sorry

theorem Perm.map {β} (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : map f l₁ ~ map f l₂ := filterMapEqMap f ▸ p.filterMap _

theorem perm_nodup_keys {β : α → Type v} {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : nodupkeys l₁ ↔ nodupkeys l₂ := (h.map _).nodup_iff

theorem permIffCount [DecidableEq α] {l₁ l₂ : List α} : l₁ ~ l₂ ↔ (∀ a, count a l₁ = count a l₂) := sorry

theorem perm.eraseDup [DecidableEq α] {l₁ l₂ : List α} (p : l₁ ~ l₂) : eraseDup l₁ ~ eraseDup l₂ := sorry

def lookup' (a : α) : List (Sigma β) → Option (β a)
| []             => none
| (⟨a', b⟩ :: l) => sorry -- if h : a' = a then some (Eq.recOn h b) else lookup' l

theorem permLookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) : lookup' a l₁ = lookup' a l₂ := sorry

def attach (l : List α) : List {x // x ∈ l} := sorry

@[simp] lemma attach_eq_nil (l : List α) : l.attach = [] ↔ l = [] := sorry

@[simp] theorem mem_attach (l : List α) : ∀ x, x ∈ l.attach := sorry

inductive forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil : forall₂ R [] []
  | cons {a b l₁ l₂} : R a b → forall₂ R l₁ l₂ → forall₂ R (a::l₁) (b::l₂)

theorem forall₂_iff {α β} (R : α → β → Prop) (l₁ : List α) (l₂ : List β) :
  (forall₂ R l₁ l₂) ↔ (l₁ = [] ∧ l₂ = []) ∨ ∃ hd₁ hd₂ tl₁ tl₂, R hd₁ hd₂ ∧ forall₂ R tl₁ tl₂ ∧ l₁ = hd₁ :: tl₁ ∧ l₂ = hd₂ :: tl₂ := 
  sorry

end List