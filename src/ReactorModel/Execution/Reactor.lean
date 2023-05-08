import ReactorModel.Execution.Dependency

noncomputable section
open Classical

namespace ReactorType

variable [Indexable α] in section

def dependencies (rtr : α) (rcn : ID) : Set ID := 
  { rcn' | rcn' <[rtr] rcn }

structure Refresh (rtr₁ rtr₂ : α) (acts : ID ⇀ Value) : Prop where
  equiv    : rtr₁ ≈ rtr₂
  eq_state : rtr₂[.stv] = rtr₁[.stv]
  acts     : rtr₂[.act] = acts
  inputs   : rtr₂[.inp] = rtr₁[.inp].map fun _ => .absent
  outputs  : rtr₂[.out] = rtr₁[.out].map fun _ => .absent

end

variable [Proper α] [Finite α]

def refresh (rtr : α) (acts : ID ⇀ Value) : α :=
  let rtr₁ := set rtr  .inp $ Partial.const (rtr[.inp].ids : Set ID) .absent
  let rtr₂ := set rtr₁ .out $ Partial.const (rtr[.out].ids : Set ID) .absent
  set rtr₂ .act acts

end ReactorType