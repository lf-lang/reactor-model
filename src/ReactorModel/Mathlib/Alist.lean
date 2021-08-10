import ReactorModel.Mathlib.List

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