import ReactorModel.Objects.Reactor.Raw

namespace Reactor
namespace Raw

-- About the `↔`-condition in `prio`:  We want to establish a dependency between mutations with 
-- priorities  as well normal reactions with priorities, but not between normal reactions and
-- mutations. Otherwise a normal reaction might take precedence over a mutation. Also the precedence
-- of mutations over normal reactions is handled by `mutNorm` - so this would potentially just 
-- create  a redundancy.
inductive Dependency (rtr : Reactor.Raw) : ID → ID → Prop
  | prio :
    (rtr.con? .rcn i₁ = rtr.con? .rcn i₂) → (rtr[.rcn][i₁] = some rcn₁) → 
    (rtr[.rcn][i₂] = some rcn₂) → (rcn₁.Mutates ↔ rcn₂.Mutates) → (rcn₁.prio > rcn₂.prio) → 
    Dependency rtr i₁ i₂
  | mutNorm : 
    (rtr.con? .rcn iₘ = rtr.con? .rcn iₙ) → (rtr[.rcn][iₘ] = some m) → (rtr[.rcn][iₙ] = some n) →
    (m.Mutates) → (n.Normal) → Dependency rtr iₘ iₙ
  | depOverlap :
    (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) →
    (rcn₁.deps .out ∩ rcn₂.deps .in).Nonempty → Dependency rtr i₁ i₂
  | mutNest :
    (rtr[.rcn][iₘ] = some m) → (m.Mutates) → (rtr.con? .rcn iₘ = some rtr₁) →
    (rtr₁.obj.nest j = some rtr₂) → (iᵣ ∈ rtr₂.rcns.ids) → Dependency rtr iₘ iᵣ
  | trans : 
    Dependency rtr i₁ i₂ → Dependency rtr i₂ i₃ → Dependency rtr i₁ i₃

def Dependency.Acyclic (rtr : Reactor.Raw) : Prop :=
  ∀ i, ¬Dependency rtr i i 

theorem Dependency.Acyclic.nested (a : Acyclic rtr₁) (h : rtr₁.nest i = some rtr₂) : Acyclic rtr₂ :=
  sorry

end Raw 
end Reactor