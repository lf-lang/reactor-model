import ReactorModel.Mathlib.List

def Multiset.{u} (α : Type u) : Type u := Quotient ⟨List.Perm (α := α), List.Perm.Equivalence⟩

instance : Coe (List α) (Multiset α) := ⟨Quotient.mk'⟩

namespace Multiset

def nodup (s : Multiset α) : Prop := Quot.liftOn s List.Nodup (λ _ _ p => propext p.nodup_iff)

def mem (a : α) (s : Multiset α) : Prop := Quot.liftOn s (λ l => a ∈ l) (λ l₁ l₂ (e : l₁ ~ l₂) => propext e.mem_iff)

def nodupkeys {β : α → Type _} (s : Multiset (Sigma β)) : Prop := Quot.liftOn s List.nodupkeys (λ s t p => propext $ List.perm_nodup_keys p)

def map (f : α → β) (s : Multiset α) : Multiset β := sorry

def keys {β : α → Type _} (s : Multiset (Sigma β)) : Multiset α := s.map Sigma.fst

def sum : Multiset α → α := sorry

def join : Multiset (Multiset α) → Multiset α := sum

def bind (s : Multiset α) (f : α → Multiset β) : Multiset β := join (map f s)

def eraseDup [DecidableEq α] (s : Multiset α) : Multiset α := sorry

theorem nodupEraseDup [DecidableEq α] (s : Multiset α) : s.eraseDup.nodup := sorry

instance : Membership α (Multiset α) := ⟨Multiset.mem⟩

instance : EmptyCollection (Multiset α) := ⟨@List.nil α⟩

theorem nodupEmpty : @nodup α ∅ := List.Pairwise.nil

end Multiset