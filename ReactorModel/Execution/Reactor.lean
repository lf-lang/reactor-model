import ReactorModel.Execution.Dependency

noncomputable section
open Classical

namespace Reactor

variable [Hierarchical α] in section

def dependencies (rtr : α) (rcn : α✦) : Set α✦ :=
  { rcn' | rcn' <[rtr] rcn }

structure Refresh (rtr₁ rtr₂ : α) (acts : α✦ ⇀ α◾) : Prop where
  equiv    : rtr₁ ≈ rtr₂
  eq_state : rtr₂[.stv] = rtr₁[.stv]
  acts     : rtr₂[.act] = acts
  inputs   : rtr₂[.inp] = rtr₁[.inp].map fun _ => ⊥
  outputs  : rtr₂[.out] = rtr₁[.out].map fun _ => ⊥

end

variable [Proper α] [Finite α]

def refresh (rtr : α) (acts : α✦ ⇀ α◾) : α :=
  let rtr₁ := set rtr  .inp <| Partial.const (rtr[.inp].ids : Set α✦) ⊥
  let rtr₂ := set rtr₁ .out <| Partial.const (rtr[.out].ids : Set α✦) ⊥
  set rtr₂ .act acts

end Reactor
