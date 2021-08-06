import Mathlib

namespace Option 

protected def elim : Option α → β → (α → β) → β
  | (some x), y, f => f x
  | none,     y, f => y

instance Bind : Bind (Option) := ⟨Option.bind⟩

end Option

namespace List

variable (r : α → α → Prop)

inductive pairwise : List α → Prop
  | nil : pairwise []
  | cons : ∀ {a : α} {l : List α}, (∀ a' ∈ l, r a a') → pairwise l → pairwise (a::l)

def pwFilter (R : α → α → Prop) [DecidableRel R] : List α → List α
| []        => []
| (x :: xs) => 
  let IH := pwFilter R xs
  sorry -- if ∀ y, y ∈ IH → R x y then x :: IH else IH

theorem pairwisePWFilter {R : α → α → Prop} [DecidableRel R] : ∀ (l : List α), pairwise R (pwFilter R l)
| []       => pairwise.nil
| (x :: l) => sorry

def nodup : List α → Prop := pairwise (. ≠ .)

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

instance isSetoid (α) : Setoid (List α) :=
  Setoid.mk _ perm.eqv

theorem perm.lengthEq {l₁ l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := by
  induction p with
  | nil => rfl
  | cons _ _ h => simp [h]
  | swap => simp
  | trans _ _ h₁ h₂ => exact Eq.trans h₁ h₂

theorem perm.eqNil {l : List α} (p : l ~ []) : l = [] :=
  eq_nil_of_length_eq_zero p.lengthEq

theorem perm.nilEq {l : List α} (p : [] ~ l) : [] = l :=
  p.symm.eqNil.symm

theorem perm.subset {l₁ l₂ : List α} (p : l₁ ~ l₂) [DecidableEq α]: l₁ ⊆ l₂ := by
induction p with
 | nil =>
   intro x
   exfalso
 | @cons x l₁ l₂ p h  =>
   intros y h_y_in_x_cons_l₁
   apply List.mem_cons.2
   by_cases hxy : (y = x)
   -- y = x
   apply Or.inl
   exact hxy
   -- y != x
   have horl₁  := List.mem_cons.1 h_y_in_x_cons_l₁
   cases horl₁ with
    | inl heq => contradiction
    | inr hl₁ =>
      apply Or.inr
      apply h
      exact hl₁
 | swap x y l =>
   intros a ha
   have ha' := List.mem_cons.1 ha
   apply List.mem_cons.2
   cases ha' with
    -- a = y
    | inl heq =>
      apply Or.inr
      apply List.mem_cons.2
      apply Or.inl
      exact heq
    -- a ∈ x :: l
    | inr h_in_x_cons_l =>
    have hxl := List.mem_cons.1 h_in_x_cons_l
    cases hxl with
    -- a = x
    | inl heq =>
       apply Or.inl
       exact heq
    | inr h_in_l =>
      apply Or.inr
      apply List.mem_cons.2
      apply Or.inr
      exact h_in_l
 | trans _ _ h_l₁_subseteq_l₂ h_l₂_subseteq_l₃  =>
   intros x hx
   apply h_l₂_subseteq_l₃
   apply h_l₁_subseteq_l₂
   exact hx

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

theorem perm.consInv {a : α} {l₁ l₂ : List α} : a::l₁ ~ a::l₂ → l₁ ~ l₂ := by
intro h
-- need to bring hypothesis to form l₁' ~ l₂' for induction
generalize hl₁' : (a::l₁)  = l₁'
generalize hl₂' : (a::l₂)  = l₂'
rw [hl₁'] at h
rw [hl₂'] at h
-- now we can do induction
induction h with
| nil =>
contradiction
| cons =>
sorry
| swap =>
sorry
| trans =>
sorry

theorem perm.pairwiseIff {R : α → α → Prop} (S : ∀ {x y}, R x y → R y x) [DecidableEq α]:
  ∀ {l₁ l₂ : List α} (p : l₁ ~ l₂), pairwise R l₁ ↔ pairwise R l₂ := by
  suffices ∀ {l₁ l₂}, l₁ ~ l₂ → pairwise R l₁ → pairwise R l₂ 
  from λ l₁ l₂ p => ⟨this p, this p.symm⟩
  intro l₁ l₂ p d
  induction d generalizing l₂ with
  | nil => 
    rw [←p.nilEq]
    constructor
  | @cons a l₁ h d IH =>
    have : a ∈ l₂ := p.subset (mem_cons_self _ _)
    cases (mem_split this)
    sorry
    /-have p' := (p.trans perm.permMiddle).cons_inv
    rcases mem_split this with ⟨s₂, t₂, rfl⟩,
    have p' := (p.trans perm_middle).cons_inv,
    refine (pairwise_middle S).2 (pairwise_cons.2 ⟨λ b m, _, IH _ p'⟩),
    exact h _ (p'.symm.subset m)
    -/

theorem perm.nodupIff [DecidableEq α] {l₁ l₂ : List α} : l₁ ~ l₂ → (List.nodup l₁ ↔ List.nodup l₂) :=
  perm.pairwiseIff Ne.symm

theorem perm.memIff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
  sorry -- Iff.intro (λ m => h.subset m) (λ m => h.symm.subset m)

def keys {β : α → Type v} : List (Sigma β) → List α :=
  map Sigma.fst

def nodupkeys {β : α → Type v} (l : List (Sigma β)) : Prop :=
  l.keys.nodup

theorem filterMapConsSome (f : α → Option β) (a : α) (l : List α) {b : β} (h : f a = some b) :
  filterMap f (a :: l) = b :: filterMap f l :=
  by simp only [filterMap, h] ; split 

theorem filterMapEqMap (f : α → β) : filterMap (some ∘ f) = map f := by
  funext l
  induction l with 
  | nil => rfl
  | cons a l IH => 
    simp only [filterMapConsSome (some ∘ f) _ _ rfl, IH, map_cons]
    split

theorem perm.filterMap (f : α → Option β) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
  filterMap f l₁ ~ filterMap f l₂ := sorry

theorem perm.map {β} (f : α → β) {l₁ l₂ : List α} (p : l₁ ~ l₂) :
  map f l₁ ~ map f l₂ :=
  filterMapEqMap f ▸ p.filterMap _

theorem permNodupkeys [DecidableEq α] {β : α → Type v} {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : nodupkeys l₁ ↔ nodupkeys l₂ :=
  (h.map _).nodupIff

def countp (p : α → Prop) [DecidablePred p] : List α → Nat
| []      => 0
| (x::xs) => if p x then Nat.succ (countp p xs) else countp p xs

def count [DecidableEq α] (a : α) : List α → Nat := countp (Eq a)

theorem permIffCount [DecidableEq α] {l₁ l₂ : List α} : l₁ ~ l₂ ↔ (∀ a, count a l₁ = count a l₂) :=
  sorry

theorem perm.eraseDup [DecidableEq α] {l₁ l₂ : List α} (p : l₁ ~ l₂) : eraseDup l₁ ~ eraseDup l₂ :=
  sorry

def lookup' (a : α) : List (Sigma β) → Option (β a)
| []             => none
| (⟨a', b⟩ :: l) => sorry -- if h : a' = a then some (Eq.recOn h b) else lookup' l

theorem permLookup (a : α) {l₁ l₂ : List (Sigma β)}
  (nd₁ : l₁.nodupkeys) (nd₂ : l₂.nodupkeys) (p : l₁ ~ l₂) : lookup' a l₁ = lookup' a l₂ :=
  sorry

end List

def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

instance : Coe (List α) (Multiset α) := ⟨Quotient.mk⟩

namespace Multiset

def nodup [DecidableEq α] (s : Multiset α) : Prop :=
  Quot.liftOn s List.nodup (λ _ _ p => propext p.nodupIff)

def mem (a : α) (s : Multiset α) : Prop :=
  Quot.liftOn s (λ l => a ∈ l) (λ l₁ l₂ (e : l₁ ~ l₂) => propext e.memIff)

def nodupkeys [DecidableEq α] {β : α → Type _} (s : Multiset (Sigma β)) : Prop :=
  Quot.liftOn s List.nodupkeys (λ s t p => propext $ List.permNodupkeys p)

-- I couldn't find a specific instance for coercing lists to multisets in Lean 3,
-- so I'm guessing that may have been implemented for quotient types in general.
-- It seems that hasn't been implemented yet in Lean 4.
-- This also affects Alist.toFinmap and Multiset.nodupEraseDup
def map (f : α → β) (s : Multiset α) : Multiset β :=
-- Quot.liftOn s (λ l : List α => (l.map f : Multiset β)) (λ l₁ l₂ p => Quot.sound (p.map f))
  sorry

def keys {β : α → Type _} (s : Multiset (Sigma β)) : Multiset α :=
  s.map Sigma.fst

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/multiset.2Esum
def sum : Multiset α → α := sorry

def join : Multiset (Multiset α) → Multiset α := sum

def bind (s : Multiset α) (f : α → Multiset β) : Multiset β :=
  join (map f s)

def eraseDup [DecidableEq α] (s : Multiset α) : Multiset α :=
  sorry
  -- Quot.liftOn s (λ l => (l.eraseDup : Multiset α)) (λ s t p => Quot.sound p.eraseDup)

theorem nodupEraseDup [DecidableEq α] (s : Multiset α) : s.eraseDup.nodup :=
  sorry
  -- Quot.inductionOn s List.nodupEraseDup

instance : Mem α (Multiset α) := ⟨Multiset.mem⟩

instance : EmptyCollection (Multiset α) := ⟨@List.nil α⟩

theorem nodupEmpty [DecidableEq α] : @nodup α _ ∅ := List.pairwise.nil

end Multiset

structure Finset (α) [DecidableEq α] where
  val : Multiset α
  nodup : Multiset.nodup val

def Multiset.toFinset [DecidableEq α] (s : Multiset α) : Finset α := ⟨_, nodupEraseDup s⟩

namespace Finset

instance [DecidableEq α] : Mem α (Finset α) := ⟨λ a f => a ∈ f.val⟩

instance [DecidableEq α] : EmptyCollection (Finset α) := ⟨{ val := ∅, nodup := Multiset.nodupEmpty }⟩

protected def bUnion [DecidableEq α] [DecidableEq β] (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.val.bind (λ a => (t a).val)).toFinset

def singleton [DecidableEq α] (a : α) : Finset α := ⟨[a], sorry⟩

instance [DecidableEq α] : Coe (Finset α) (Set α) := ⟨λ f => {x | x ∈ f}⟩

end Finset

namespace Set 

def finite [DecidableEq α] (s : Set α) : Prop :=
  ∃ f : Finset α, ∀ a, a ∈ s ↔ a ∈ f

noncomputable def finite.toFinset [DecidableEq α] {s : Set α} (h : s.finite) : Finset α :=
  Classical.choose h

end Set

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

structure Finmap {α : Type u} [DecidableEq α] (β : α → Type v) : Type (max u v) where
  entries : Multiset (Sigma β)
  nodupkeys : entries.nodupkeys

def Alist.toFinmap [DecidableEq α] {β : α → Type _} (s : Alist β) : Finmap β := sorry -- ⟨s.entries, s.nodupkeys⟩

namespace Finmap

infix:50 " ⇀ " => (λ a b [DecidableEq a] => Finmap (λ _ : a => b))

def liftOn
  [DecidableEq α] {β : α → Type v} {γ} (s : Finmap β) (f : Alist β → γ)
  (H : ∀ a b : Alist β, a.entries ~ b.entries → f a = f b) : γ :=
  sorry

def lookup [DecidableEq α] {β : α → Type _} (a : α) (s : Finmap β) : Option (β a) :=
  liftOn s (Alist.lookup a) (λ s t => Alist.permLookup)

theorem inductionOn [DecidableEq α] {β : α → Type _} {C : Finmap β → Prop} (s : Finmap β) (H : ∀ (a : Alist β), C a.toFinmap) : C s := by
  -- by rcases s with ⟨⟨a⟩, h⟩; exact H ⟨a, h⟩
  sorry

def keys [DecidableEq α] {β : α → Type _} (s : Finmap β) : Finset α :=
  sorry -- ⟨s.entries.keys, inductionOn s keys_nodup⟩

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