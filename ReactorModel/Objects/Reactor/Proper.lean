import ReactorModel.Objects.Reactor.Extensional
import ReactorModel.Objects.Reactor.Hierarchical
import ReactorModel.Objects.Reactor.WellFounded
import ReactorModel.Objects.Reactor.Updatable

namespace Reactor
namespace Wellformed

-- `ValidDependency rtr rk dk d` means that in reactor `rtr`, reactions of kind `rk` can have `d` as
-- a valid dependency target of kind `dk`. For example `ValidDependency rtr .mut .out (.port .in i)`
-- states that mutations can specify the input port identified by `i` as effect and
-- `ValidDependency rtr .norm .in (.action i)` states that normal reactions can specify the action
-- identified by `i` as source.
inductive ValidDependency [Reactor α] (rtr : α) :
    Reaction.Kind → Kind → Reaction.Dependency _ → Prop where
  | inp       : (i ∈ rtr{.inp})                             → ValidDependency _ _     .in  ⟨.inp, i⟩
  | out       : (i ∈ rtr{.out})                             → ValidDependency _ _     .out ⟨.out, i⟩
  | stv       : (i ∈ rtr{.stv})                             → ValidDependency _ _     _    ⟨.stv, i⟩
  | act       : (i ∈ rtr{.act})                             → ValidDependency _ _     _    ⟨.act, i⟩
  | nestedIn  : (rtr{.rtr}{j} = some con) → (i ∈ con{.inp}) → ValidDependency _ _     .out ⟨.inp, i⟩
  | nestedOut : (rtr{.rtr}{j} = some con) → (i ∈ con{.out}) → ValidDependency _ .norm .in  ⟨.out, i⟩

-- Note: This proposition is only meaningful under the condition that `rcn₁` and `rcn₂` live in the
--       same reactor.
inductive NeedOrderedPriority
    [Identifiable α] [Valued α] [Prioritizable α] (rcn₁ rcn₂ : Reaction α) : Prop
  | overlap (h₁ : d ∈ rcn₁.deps .out) (h₂ : d ∈ rcn₂.deps .out)
  | hazard (h₁ : ⟨.stv, s⟩ ∈ rcn₁.deps k₁) (h₂ : ⟨.stv, s⟩ ∈ rcn₂.deps k₂) (ho : k₁ = .out ∨ k₂ = .out)
  | mutation (h₁ : rcn₁.Mutates) (h₂ : rcn₂.Mutates)

end Wellformed

open Wellformed

structure Wellformed [idx : Hierarchical α] (rtr : α) : Prop where
  unique_inputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) →
                  (⟨.inp, i⟩ ∈ rcn₁.deps .out) → (⟨.inp, i⟩ ∉ rcn₂.deps .out)
  ordered_prio  : (rtr[.rtr][i] = some con) → (con{.rcn}{i₁} = some rcn₁) →
                  (con{.rcn}{i₂} = some rcn₂) → (i₁ ≠ i₂) → (NeedOrderedPriority rcn₁ rcn₂) →
                  (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  valid_deps    : (rtr[.rtr][i] = some con) → (con{.rcn}{j} = some rcn) → (d ∈ rcn.deps k) →
                  (ValidDependency con rcn.kind k d)

-- TODO: Is there some other way to reference the `Hierarchical α` instance, without constructing it
--       explicitly.
class Proper (α) extends Extensional α, Hierarchical α, WellFounded α, LawfulUpdatable α where
  wellformed : ∀ rtr : α, Wellformed rtr (idx := ⟨unique_ids⟩)

end Reactor
