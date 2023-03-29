import ReactorModel.Primitives
import Mathlib.Data.Finset.Lattice

namespace Action

def schedule (a : Action) (t : Time) (v : Value) : Action :=
  match a.tags.filter (·.time = t) |>.max with
  | ⊥           => a.insert ⟨t, 0⟩ v
  | some ⟨_, m⟩ => a.insert ⟨t, m + 1⟩ v

end Action