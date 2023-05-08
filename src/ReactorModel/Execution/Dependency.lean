import ReactorModel.Objects

open ReactorType

variable [Indexable α]

-- About the `↔`-condition in `prio`:  We want to establish a dependency between mutations with 
-- priorities as well normal reactions with priorities, but not between normal reactions and
-- mutations. Otherwise a normal reaction might take precedence over a mutation. Also the precedence
-- of mutations over normal reactions is handled by `mutNorm`, so this would potentially create a
-- redundancy.
--
-- Note: `Dependency rtr i₁ i₂` means that in `i₁` must occur before `i₂`. 
inductive Dependency (rtr : α) : ID → ID → Prop
  | prio : 
    (rtr[.rtr][i] = some con) → (con{.rcn}{i₁} = some rcn₁) → (con{.rcn}{i₂} = some rcn₂) → 
    (rcn₁.Mutates ↔ rcn₂.Mutates) → (rcn₁.prio > rcn₂.prio) → Dependency rtr i₁ i₂
  | depOverlap {d : Reaction.Dependency} :
    (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (d ∈ rcn₁.deps .out) → 
    (d ∈ rcn₂.deps .in) → (d.cpt ≠ .stv) → Dependency rtr i₁ i₂
  | mutNorm : 
    (rtr[.rtr][i] = some con) → (con{.rcn}{iₘ} = some m) → (con{.rcn}{iₙ} = some n) → (m.Mutates) → 
    (n.Normal) → Dependency rtr iₘ iₙ
  | mutNest :
    (rtr[.rtr][i] = some rtr₁) → (rtr₁{.rtr}{j} = some rtr₂) → (rtr₁{.rcn}{iₘ} = some m) → 
    (m.Mutates) → (iᵣ ∈ rtr₂{.rcn}) → Dependency rtr iₘ iᵣ
  | trans : 
    Dependency rtr i₁ i₂ → Dependency rtr i₂ i₃ → Dependency rtr i₁ i₃

notation i₁ " <[" rtr "] " i₂ => Dependency rtr i₁ i₂

def Dependency.Acyclic (rtr : α) : Prop :=
  ∀ i, ¬(i <[rtr] i)