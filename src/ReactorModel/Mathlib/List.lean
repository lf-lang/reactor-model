import Mathlib

namespace List

def findIndex (p : α → Prop) [DecidablePred p] : List α → Nat
  | []     => 0
  | (a::l) => if p a then 0 else Nat.succ (findIndex p l)

def indexOf [DecidableEq α] (a : α) : List α → Nat := findIndex (Eq a)

theorem index_of_cons_self [DecidableEq α] (a : α) (l : List α) : 
  indexOf a (a::l) = 0 := 
  sorry

variable (r : α → α → Prop)

inductive pairwise : List α → Prop
  | nil : pairwise []
  | cons : ∀ {a : α} {l : List α}, (∀ a' ∈ l, r a a') → pairwise l → pairwise (a::l)

def pwFilter (R : α → α → Prop) [DecidableRel R] : List α → List α
  | []        => []
  | (x :: xs) => sorry

theorem pairwisePWFilter {R : α → α → Prop} [DecidableRel R] : 
  ∀ (l : List α), pairwise R (pwFilter R l) := 
  sorry

def nodup : List α → Prop := pairwise (. ≠ .)

theorem nodup_erase_of_nodup [DecidableEq α] (a : α) {l} : 
  nodup l → nodup (l.erase a) := 
  sorry

-- From the old "mathlib.lean"
theorem index_of_erase_lt {α : Type _} [DecidableEq α] {l : List α} {e x x' : α} (h : l.indexOf x < l.indexOf x') (hₘ : x ∈ l.erase e) (hₘ' : x' ∈ l.erase e) (hₙ : l.nodup) :
  (l.erase e).indexOf x < (l.erase e).indexOf x' := 
  sorry

def eraseDup [DecidableEq α] : List α → List α := pwFilter (. ≠ .)

theorem nodupEraseDup [DecidableEq α] : ∀ l : List α, l.eraseDup.nodup := pairwisePWFilter

inductive perm : List α → List α → Prop
  | nil   : perm [] []
  | cons  : ∀ (x : α) {l₁ l₂ : List α}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
  | swap  : ∀ (x y : α) (l : List α), perm (y::x::l) (x::y::l)
  | trans : ∀ {l₁ l₂ l₃ : List α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

infix:50 " ~ " => perm

protected theorem perm.refl : ∀ (l : List α), l ~ l
  | []      => perm.nil
  | (x::xs) => (perm.refl xs).cons x

protected theorem perm.symm {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₂ ~ l₁ := by
  induction p with
  | nil => exact nil
  | cons x _ p => exact cons x p
  | swap x y l => exact swap y x l
  | trans _ _ p₁ p₂ => exact trans p₂ p₁

theorem perm.eqv : Equivalence (@perm α) where
  refl := perm.refl
  symm := perm.symm
  trans := perm.trans

instance isSetoid (α) : Setoid (List α) := Setoid.mk _ perm.eqv

theorem perm_ext {l₁ l₂ : List α} (d₁ : nodup l₁) (d₂ : nodup l₂) : 
  l₁ ~ l₂ ↔ ∀a, a ∈ l₁ ↔ a ∈ l₂ := 
  sorry

theorem perm.mem_iff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : 
  a ∈ l₁ ↔ a ∈ l₂ :=
  sorry

theorem perm.lengthEq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ h => simp [h]
  | swap => simp
  | trans _ _ h₁ h₂ => exact Eq.trans h₁ h₂

theorem perm.eqNil {l : List α} (p : l ~ []) : 
  l = [] := 
  eq_nil_of_length_eq_zero p.lengthEq

theorem perm.nilEq {l : List α} (p : [] ~ l) : 
  [] = l := 
  p.symm.eqNil.symm

theorem perm.subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : 
  l₁ ⊆ l₂ := 
  sorry

theorem perm.permMiddle {a : α} : ∀ {l₁ l₂ : List α}, l₁++a::l₂ ~ a::(l₁++l₂) := by
  intros l₁
  induction l₁ with
  | nil =>
    simp
    intros l₂
    apply perm.refl
  | @cons b l₁ IH =>
    intro l₂
    have IH' := @IH (l₂)
    have IH'' := perm.cons b IH'
    have Sab :=  (swap a b (l₁ ++ l₂))
    have T := perm.trans IH'' Sab
    simp [T]

theorem perm.consInv {a : α} {l₁ l₂ : List α} : a::l₁ ~ a::l₂ → l₁ ~ l₂ := sorry

theorem perm.pairwiseIff {R : α → α → Prop} (S : ∀ {x y}, R x y → R y x) : ∀ {l₁ l₂ : List α} (p : l₁ ~ l₂), pairwise R l₁ ↔ pairwise R l₂ := sorry

theorem perm.nodupIff {l₁ l₂ : List α} : l₁ ~ l₂ → (List.nodup l₁ ↔ List.nodup l₂) := perm.pairwiseIff Ne.symm

theorem perm.memIff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ := sorry

def keys {β : α → Type v} : List (Sigma β) → List α := map Sigma.fst

def nodupkeys {β : α → Type v} (l : List (Sigma β)) : Prop := l.keys.nodup

theorem filterMapConsSome (f : α → Option β) (a : α) (l : List α) {b : β} (h : f a = some b) : filterMap f (a :: l) = b :: filterMap f l := sorry

theorem filterMapEqMap (f : α → β) : filterMap (some ∘ f) = map f := sorry

theorem perm.filterMap (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : filterMap f l₁ ~ filterMap f l₂ := sorry

theorem perm.map {β} (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) : map f l₁ ~ map f l₂ := filterMapEqMap f ▸ p.filterMap _

theorem permNodupkeys {β : α → Type v} {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : nodupkeys l₁ ↔ nodupkeys l₂ := (h.map _).nodupIff

def countp (p : α → Prop) [DecidablePred p] : List α → Nat
| []      => 0
| (x::xs) => if p x then Nat.succ (countp p xs) else countp p xs

def count [DecidableEq α] (a : α) : List α → Nat := countp (Eq a)

theorem permIffCount [DecidableEq α] {l₁ l₂ : List α} : l₁ ~ l₂ ↔ (∀ a, count a l₁ = count a l₂) := sorry

theorem perm.eraseDup [DecidableEq α] {l₁ l₂ : List α} (p : l₁ ~ l₂) : eraseDup l₁ ~ eraseDup l₂ := sorry

def lookup' (a : α) : List (Sigma β) → Option (β a)
| []             => none
| (⟨a', b⟩ :: l) => sorry -- if h : a' = a then some (Eq.recOn h b) else lookup' l

theorem permLookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) : lookup' a l₁ = lookup' a l₂ := sorry

end List