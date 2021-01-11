import data.set.basic

def partial_nondet_func (α : Type*) (β : α → Type*) : Type* := 
  Π a : α, set (β a) 

notation α `~?>` β := partial_nondet_func α (λ _, β)
notation α `~?>` β := partial_nondet_func α β

def partial_nondet_func.is_total {α : Type*} {β : α → Type*} (f : α ~?> β) : Prop :=
  ∀ a, (f a).nonempty

structure total_nondet_func (α : Type*) (β : α → Type*) := 
  (func : α ~?> β)
  (total : func.is_total)

notation α `~>` β := total_nondet_func α (λ _, β)
notation α `~>` β := total_nondet_func α β

instance coe_total_nondet_func {α : Type*} {β : α → Type*} : has_coe_to_fun (α ~> β) := 
  ⟨_, (λ f, f.func)⟩

def total_nondet_func.is_det {α : Type*} {β : α → Type*} (f : α ~> β) : Prop :=
  ∀ a, ∃! b, (f : α ~?> β) a = {b} 

noncomputable def total_nondet_func.det {α : Type*} {β : α → Type*} (f : α ~> β) (h : f.is_det) : Π a : α, β a :=
  λ a : α, (h a).some 
