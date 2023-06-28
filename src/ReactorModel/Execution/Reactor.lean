import ReactorModel.Execution.Dependency

noncomputable section
open Classical

namespace Reactor

variable [Hierarchical α] in section

def dependencies (rtr : α) (rcn : ID) : Set ID := 
  { rcn' | rcn' <[rtr] rcn }

structure Refresh (rtr₁ rtr₂ : α) (logs : ID ⇀ Value) : Prop where
  equiv    : rtr₁ ≈ rtr₂
  state    : rtr₂[.stv] = rtr₁[.stv]
  logs     : rtr₂[.log] = logs
  phys     : rtr₂[.phy] = rtr₁[.phy].map fun _ => .absent
  inputs   : rtr₂[.inp] = rtr₁[.inp].map fun _ => .absent
  outputs  : rtr₂[.out] = rtr₁[.out].map fun _ => .absent

end

variable [Proper α] [Finite α]

def refresh (rtr : α) (logs : ID ⇀ Value) : α :=
  let rtr₁ := set rtr  .inp $ Partial.const (rtr[.inp].ids : Set ID) .absent
  let rtr₂ := set rtr₁ .out $ Partial.const (rtr[.out].ids : Set ID) .absent
  let rtr₃ := set rtr₂ .phy $ Partial.const (rtr[.phy].ids : Set ID) .absent
  set rtr₃ .log logs

end Reactor