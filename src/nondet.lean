import data.set.basic

def partial_nondet_func (α β : Type*) : Type* := 
  α → set β 

notation α `~?>` β := partial_nondet_func α β 

def partial_nondet_func.is_total {α β : Type*} (f : α ~?> β) : Prop :=
  ∀ a, (f a).nonempty

structure total_nondet_func (α β : Type*) := 
  (func : α ~?> β)
  (total : func.is_total)

notation α `~>` β := total_nondet_func α β 

instance coe_total_nondet_func {α β : Type*} : has_coe_to_fun (α ~> β) := 
  ⟨(λ _, α → set β), (λ f, f.func)⟩

def total_nondet_func.is_det {α β : Type*} (f : α ~> β) : Prop :=
  ∀ a, ∃! b, (f : α ~?> β) a = {b} 

noncomputable def total_nondet_func.det {α β : Type*} (f : α ~> β) (h : f.is_det) : α → β :=
  λ a : α, (h a).some 
