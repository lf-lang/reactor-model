import ReactorModel.Objects.Reactor.Extensional
import ReactorModel.Objects.Reactor.Indexable
import ReactorModel.Objects.Reactor.WellFounded

namespace ReactorType
namespace Wellformed

-- `ValidDependency rtr rk dk d` means that in reactor `rtr`, reactions of kind `rk` can have `d` as 
-- a valid dependency target of kind `dk`. For example `ValidDependency rtr .mut .out (.port .in i)` 
-- states that mutations can specify the input port identified by `i` as effect and 
-- `ValidDependency rtr .norm .in (.action i)` states that normal reactions can specify the action 
-- identified by `i` as source.
inductive ValidDependency [ReactorType α] (rtr : α) : 
    Reaction.Kind → Kind → Reaction.Dependency → Prop
  | inp       : i ∈ rtr{.inp}                           → ValidDependency rtr _     .in  ⟨.inp, i⟩   
  | out       : i ∈ rtr{.out}                           → ValidDependency rtr _     .out ⟨.out, i⟩   
  | stv       : i ∈ rtr{.stv}                           → ValidDependency rtr _     _    ⟨.stv, i⟩  
  | act       : i ∈ rtr{.act}                           → ValidDependency rtr _     _    ⟨.act, i⟩
  | nestedIn  : rtr{.rtr}{j} = some con → i ∈ con{.inp} → ValidDependency rtr _     .out ⟨.inp, i⟩
  | nestedOut : rtr{.rtr}{j} = some con → i ∈ con{.out} → ValidDependency rtr .norm .in  ⟨.out, i⟩ 

-- Note: This proposition is only meaningful under the condition that `rcn₁` and `rcn₂` live in the 
--       same reactor.
inductive NeedOrderedPriority (rcn₁ rcn₂ : Reaction) : Prop
  | overlap (h₁ : d ∈ rcn₁.deps .out) (h₂ : d ∈ rcn₂.deps .out)
  | hazard (h₁ : ⟨.stv, s⟩ ∈ rcn₁.deps k₁) (h₂ : ⟨.stv, s⟩ ∈ rcn₂.deps k₂) (ho : k₁ = .out ∨ k₂ = .out)
  | mutation (h₁ : rcn₁.Mutates) (h₂ : rcn₂.Mutates)

end Wellformed

open Wellformed

structure Wellformed [idx : Indexable α] (rtr : α) : Prop where
  unique_inputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → 
                  (⟨.inp, i⟩ ∈ rcn₁.deps .out) → (⟨.inp, i⟩ ∉ rcn₂.deps .out)  
  ordered_prio  : (rtr[.rtr][i] = some con) → (con{.rcn}{i₁} = some rcn₁) → 
                  (con{.rcn}{i₂} = some rcn₂) → (i₁ ≠ i₂) → (NeedOrderedPriority rcn₁ rcn₂) → 
                  (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  valid_deps    : (rtr[.rtr][i] = some con) → (con{.rcn}{j} = some rcn) → (d ∈ rcn.deps k) → 
                  (ValidDependency con rcn.kind k d) 

class Proper (α) extends Extensional α, Indexable α, WellFounded α where
  wellformed : ∀ rtr : α, Wellformed rtr (idx := toIndexable)

end ReactorType