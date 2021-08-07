import Mathlib

namespace Tactics

/-syntax "unfold " ident+ : tactic

macro_rules 
  | `(unfold $[$l:ident]+) => `(simp only [$[$l],+])-/

macro "obtain " t:term " := " h:ident : tactic =>
  `(match $h:ident with | $t:term => ?use)

end Tactics

namespace Option 

protected def elim : Option α → β → (α → β) → β
  | (some x), y, f => f x
  | none,     y, f => y

instance Bind : Bind (Option) := ⟨Option.bind⟩

lemma ne_none_iff_exists {o : Option α} : o ≠ none ↔ ∃ (x : α), some x = o := sorry

@[simp] theorem bind_eq_some {α β} {x : Option α} {f : α → Option β} {b : β} :
  x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b := sorry

end Option

namespace List

def findIndex (p : α → Prop) [DecidablePred p] : List α → Nat
  | []     => 0
  | (a::l) => if p a then 0 else Nat.succ (findIndex p l)

def indexOf [DecidableEq α] (a : α) : List α → Nat := findIndex (Eq a)

theorem index_of_cons_self [DecidableEq α] (a : α) (l : List α) : indexOf a (a::l) = 0 := sorry

variable (r : α → α → Prop)

inductive pairwise : List α → Prop
  | nil : pairwise []
  | cons : ∀ {a : α} {l : List α}, (∀ a' ∈ l, r a a') → pairwise l → pairwise (a::l)

def pwFilter (R : α → α → Prop) [DecidableRel R] : List α → List α
  | []        => []
  | (x :: xs) => sorry

theorem pairwisePWFilter {R : α → α → Prop} [DecidableRel R] : ∀ (l : List α), pairwise R (pwFilter R l) := sorry

def nodup : List α → Prop := pairwise (. ≠ .)

theorem nodup_erase_of_nodup [DecidableEq α] (a : α) {l} : nodup l → nodup (l.erase a) := sorry

-- From the old "mathlib.lean"
theorem index_of_erase_lt {α : Type _} [DecidableEq α] {l : List α} {e x x' : α} (h : l.indexOf x < l.indexOf x') (hₘ : x ∈ l.erase e) (hₘ' : x' ∈ l.erase e) (hₙ : l.nodup) :
  (l.erase e).indexOf x < (l.erase e).indexOf x' := sorry

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

theorem perm_ext {l₁ l₂ : List α} (d₁ : nodup l₁) (d₂ : nodup l₂) : l₁ ~ l₂ ↔ ∀a, a ∈ l₁ ↔ a ∈ l₂ := sorry

theorem perm.mem_iff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ := sorry

theorem perm.lengthEq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ h => simp [h]
  | swap => simp
  | trans _ _ h₁ h₂ => exact Eq.trans h₁ h₂

theorem perm.eqNil {l : List α} (p : l ~ []) : l = [] := eq_nil_of_length_eq_zero p.lengthEq

theorem perm.nilEq {l : List α} (p : [] ~ l) : [] = l := p.symm.eqNil.symm

theorem perm.subset {l₁ l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ := by sorry

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

def Multiset.{u} (α : Type u) : Type u := Quotient (List.isSetoid α)

instance : Coe (List α) (Multiset α) := ⟨Quotient.mk⟩

namespace Multiset

def nodup (s : Multiset α) : Prop := Quot.liftOn s List.nodup (λ _ _ p => propext p.nodupIff)

def mem (a : α) (s : Multiset α) : Prop := Quot.liftOn s (λ l => a ∈ l) (λ l₁ l₂ (e : l₁ ~ l₂) => propext e.memIff)

def nodupkeys {β : α → Type _} (s : Multiset (Sigma β)) : Prop := Quot.liftOn s List.nodupkeys (λ s t p => propext $ List.permNodupkeys p)

def map (f : α → β) (s : Multiset α) : Multiset β := sorry

def keys {β : α → Type _} (s : Multiset (Sigma β)) : Multiset α := s.map Sigma.fst

def sum : Multiset α → α := sorry

def join : Multiset (Multiset α) → Multiset α := sum

def bind (s : Multiset α) (f : α → Multiset β) : Multiset β := join (map f s)

def eraseDup [DecidableEq α] (s : Multiset α) : Multiset α := sorry

theorem nodupEraseDup [DecidableEq α] (s : Multiset α) : s.eraseDup.nodup := sorry

instance : Mem α (Multiset α) := ⟨Multiset.mem⟩

instance : EmptyCollection (Multiset α) := ⟨@List.nil α⟩

theorem nodupEmpty : @nodup α ∅ := List.pairwise.nil

end Multiset

structure Finset (α) where
  val : Multiset α
  nodup : Multiset.nodup val

def Multiset.toFinset [DecidableEq α] (s : Multiset α) : Finset α := ⟨_, nodupEraseDup s⟩

namespace Finset

instance : Mem α (Finset α) := ⟨λ a f => a ∈ f.val⟩

instance : EmptyCollection (Finset α) := ⟨{ val := ∅, nodup := Multiset.nodupEmpty }⟩

protected def bUnion [DecidableEq β] (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.val.bind (λ a => (t a).val)).toFinset

def singleton (a : α) : Finset α := ⟨[a], sorry⟩

instance : Coe (Finset α) (Set α) := ⟨λ f => {x | x ∈ f}⟩

def filter (s : Finset α) (p : α → Prop) [DecidablePred p] : Finset α := sorry

theorem ext_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ := sorry

theorem ext {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ := ext_iff.mpr

def range (n : ℕ) : Finset ℕ := sorry

@[simp] theorem mem_range : m ∈ range n ↔ m < n := sorry

@[simp] theorem mem_coe {a : α} {s : Finset α} : a ∈ (s : Set α) ↔ a ∈ s := sorry

@[simp] theorem coe_filter (p : α → Prop) [DecidablePred p] (s : Finset α) : ↑(s.filter p) = ({x ∈ (↑s : Set α) | p x} : Set α) := sorry

end Finset

namespace Set 

theorem ext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b := sorry

@[simp] theorem mem_sep_eq {s : Set α} {p : α → Prop} {x : α} : 
  x ∈ {x ∈ s | p x} ↔ (x ∈ s ∧ p x) := sorry

@[simp] theorem mem_set_of_eq {a : α} {p : α → Prop} : a ∈ {a | p a} ↔ p a := sorry

def finite (s : Set α) : Prop := sorry

noncomputable def finite.toFinset {s : Set α} (h : s.finite) : Finset α := sorry

theorem finite.mem_to_finset {s : Set α} (h : finite s) {a : α} : a ∈ h.toFinset ↔ a ∈ s := sorry

end Set

theorem Finset.finite_to_set (s : Finset α) : Set.finite (↑s : Set α) := sorry

structure Alist {α : Type u} (β : α → Type v) : Type (max u v) :=
  entries : List (Sigma β)
  nodupkeys : entries.nodupkeys

namespace Alist 

def lookup (a : α) (s : Alist β) : Option (β a) :=
  s.entries.lookup' a

theorem permLookup {a : α} {s₁ s₂ : Alist β} (p : s₁.entries ~ s₂.entries) :
  s₁.lookup a = s₂.lookup a :=
  List.permLookup _ s₁.nodupkeys s₂.nodupkeys p

end Alist

structure Finmap {α : Type u}  (β : α → Type v) : Type (max u v) where
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

infix:50 " ⇀ " => (λ a b [DecidableEq a] => Finmap (λ _ : a => b))

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