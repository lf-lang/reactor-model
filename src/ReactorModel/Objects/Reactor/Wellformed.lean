import ReactorModel.Objects.Reactor.Indexable

namespace ReactorType

open Indexable

-- About the `↔`-condition in `prio`:  We want to establish a dependency between mutations with 
-- priorities as well normal reactions with priorities, but not between normal reactions and
-- mutations. Otherwise a normal reaction might take precedence over a mutation. Also the precedence
-- of mutations over normal reactions is handled by `mutNorm`, so this would potentially create a
-- redundancy.
--
-- Note: `Dependency rtr i₁ i₂` means that in `i₁` must occur before `i₂`. 
inductive Dependency [Indexable α] (rtr : α) : ID → ID → Prop
  | prio : 
    (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → 
    (rcn₁.Mutates ↔ rcn₂.Mutates) → (rcn₁.prio > rcn₂.prio) → Dependency rtr i₁ i₂
  | depOverlap {d : Reaction.Dependency} :
    (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (d ∈ rcn₁.deps .out) → 
    (d ∈ rcn₂.deps .in) → (d.cpt ≠ .stv) → Dependency rtr i₁ i₂
  | mutNorm : 
    (rtr[.rtr][i] = some con) → (rcns con iₘ = some m) → (rcns con iₙ = some n) → (m.Mutates) → 
    (n.Normal) → Dependency rtr iₘ iₙ
  | mutNest :
    (rtr[.rtr][i] = some rtr₁) → (nest rtr₁ j = some rtr₂) → (rcns rtr₁ iₘ = some m) → (m.Mutates) →
    (iᵣ ∈ rcns rtr₂) → Dependency rtr iₘ iᵣ
  | trans : 
    Dependency rtr i₁ i₂ → Dependency rtr i₂ i₃ → Dependency rtr i₁ i₃

notation i₁ " <[" rtr "] " i₂ => Dependency rtr i₁ i₂

def Dependency.Acyclic [Indexable α] (rtr : α) : Prop :=
  ∀ i, ¬(i <[rtr] i)

namespace Wellformed

-- `ValidDependency rtr rk dk d` means that in reactor `rtr`, reactions of kind `rk` can have `d` as 
-- a valid dependency target of kind `dk`. For example `ValidDependency rtr .mut .out (.port .in i)` 
-- states that mutations can specify the input port identified by `i` as effect and 
-- `ValidDependency rtr .norm .in (.action i)` states that normal reactions can specify the action 
-- identified by `i` as source.
inductive ValidDependency [ReactorType α] (rtr : α) : 
    Reaction.Kind → Kind → Reaction.Dependency → Prop
  | stv       : (i ∈ state rtr) → ValidDependency rtr _ _ ⟨.stv, i⟩  
  | act       : (i ∈ acts rtr) → ValidDependency rtr _ _ ⟨.act, i⟩ 
  | prt       : (i ∈ ports rtr dk) → ValidDependency rtr _ dk ⟨.prt k, i⟩  
  | nestedIn  : (nest rtr j = some con) → (i ∈ ports con .in) → 
                ValidDependency rtr _ .out ⟨.prt .in, i⟩
  | nestedOut : (nest rtr j = some con) → (i ∈ ports con .out) → 
                ValidDependency rtr .norm .in ⟨.prt .in, i⟩ 

variable [Indexable α] [Indexable β] {rtr rtr₁ : α}

-- TODO: Refactor the `prio` conditions into one.
structure _root_.ReactorType.Wellformed (rtr : α) : Prop where
  unique_inputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → 
                  (i ∈ rtr[.prt .in]) → (⟨.prt .in, i⟩ ∈ rcn₁.deps .out) → 
                  (⟨.prt .in, i⟩ ∉ rcn₂.deps .out)  
  overlap_prio  : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → 
                  (rcns con i₂ = some rcn₂) → (i₁ ≠ i₂) → 
                  (rcn₁.deps .out ∩ rcn₂.deps .out).Nonempty → 
                  (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  hazards_prio  : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → 
                  (rcns con i₂ = some rcn₂) → (i₁ ≠ i₂) → (⟨.stv, s⟩ ∈ rcn₁.deps k₁) → 
                  (⟨.stv, s⟩ ∈ rcn₂.deps k₂) → (k₁ = .out ∨ k₂ = .out) → 
                  (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  mutation_prio : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → 
                  (rcns con i₂ = some rcn₂) → (i₁ ≠ i₂) → (rcn₁.Mutates) → (rcn₂.Mutates) →
                  (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  valid_deps    : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (d ∈ rcn.deps k) → 
                  (ValidDependency con rcn.kind k d) 
  acyclic_deps  : Dependency.Acyclic rtr

end Wellformed
end ReactorType