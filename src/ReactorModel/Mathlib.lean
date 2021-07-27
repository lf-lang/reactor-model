import Mathlib

namespace List

variable (r : α → α → Prop)

inductive pairwise : List α → Prop
  | nil : pairwise []
  | cons : ∀ {a : α} {l : List α}, (∀ a' ∈ l, r a a') → pairwise l → pairwise (a::l)

def nodup : List α → Prop := pairwise (. ≠ .)

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
    have p' := (p.trans perm.permMiddle).cons_inv
    /-
    rcases mem_split this with ⟨s₂, t₂, rfl⟩,
    have p' := (p.trans perm_middle).cons_inv,
    refine (pairwise_middle S).2 (pairwise_cons.2 ⟨λ b m, _, IH _ p'⟩),
    exact h _ (p'.symm.subset m)
    -/

theorem perm.nodupIff {l₁ l₂ : List α} : l₁ ~ l₂ → (List.nodup l₁ ↔ List.nodup l₂) :=
  perm.pairwiseIff Ne.symm

theorem perm.memIff {a : α} {l₁ l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
  Iff.intro (λ m => h.subset m) (λ m => h.symm.subset m)

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

theorem permNodupkeys {β : α → Type v} {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : nodupkeys l₁ ↔ nodupkeys l₂ :=
  (h.map _).nodupIff

end List

def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

namespace Multiset

def nodup (s : Multiset α) : Prop :=
  Quot.liftOn s List.nodup (λ _ _ p => propext p.nodupIff)

def mem (a : α) (s : Multiset α) : Prop :=
  Quot.liftOn s (λ l => a ∈ l) (λ l₁ l₂ (e : l₁ ~ l₂) => propext e.memIff)

def nodupkeys {β : α → Type v} (s : Multiset (Sigma β)) : Prop :=
  Quot.liftOn s List.nodupkeys (λ s t p => propext $ List.permNodupkeys p)

instance : Mem α (Multiset α) := ⟨Multiset.mem⟩

end Multiset

structure Finset (α) where
  val : Multiset α
  nodup : Multiset.nodup val

namespace Finset

instance : Mem α (Finset α) := ⟨λ a f => a ∈ f.val⟩

end Finset

structure Finmap {α : Type u} (β : α → Type v) : Type (max u v) where
  entries : Multiset (Sigma β)
  nodupkeys : entries.nodupkeys

def Set.finite (s : Set α) : Prop :=
  ∃ f : Finset α, ∀ a, a ∈ s ↔ a ∈ f
