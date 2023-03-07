import ReactorModel.Objects.Reactor.TypeClasses.Indexable

open ReactorType
open Indexable

-- About the `↔`-condition in `prio`:  We want to establish a dependency between mutations with 
-- priorities  as well normal reactions with priorities, but not between normal reactions and
-- mutations. Otherwise a normal reaction might take precedence over a mutation. Also the precedence
-- of mutations over normal reactions is handled by `mutNorm` - so this would potentially just 
-- create  a redundancy.
inductive Dependency [Indexable α] (rtr : α) : ID → ID → Prop
  | prio :
    (rtr[.rcn][i₁]& = rtr[.rcn][i₂]&) → (rtr[.rcn][i₁] = some rcn₁) → 
    (rtr[.rcn][i₂] = some rcn₂) → (rcn₁.Mutates ↔ rcn₂.Mutates) → (rcn₁.prio > rcn₂.prio) → 
    Dependency rtr i₁ i₂
  | mutNorm : 
    (rtr[.rcn][iₘ]& = rtr[.rcn][iₙ]&) → (rtr[.rcn][iₘ] = some m) → (rtr[.rcn][iₙ] = some n) →
    (m.Mutates) → (n.Normal) → Dependency rtr iₘ iₙ
  | depOverlap :
    (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) →
    (rcn₁.deps .out ∩ rcn₂.deps .in).Nonempty → Dependency rtr i₁ i₂
  | mutNest :
    (rtr[.rcn][iₘ] = some m) → (m.Mutates) → (rtr[.rcn][iₘ]& = some rtr₁) →
    (nest rtr₁.obj j = some rtr₂) → (iᵣ ∈ (rcns rtr₂).ids) → Dependency rtr iₘ iᵣ
  | trans : 
    Dependency rtr i₁ i₂ → Dependency rtr i₂ i₃ → Dependency rtr i₁ i₃

def Dependency.Acyclic [Indexable α] (rtr : α) : Prop :=
  ∀ i, ¬Dependency rtr i i 

variable [Indexable α]

theorem Dependency.Acyclic.nested {rtr₁ : α} (a : Acyclic rtr₁) (h : nest rtr₁ i = some rtr₂) : 
    Acyclic rtr₂ :=
  sorry

namespace ReactorType
namespace Wellformed

inductive NormalDependency (rtr : α) (i : ID) (k : Kind) : Prop
  | act  (h : i ∈ (acts rtr).ids)
  | prt  (h : ports rtr i = some ⟨v, k⟩)
  | nest (c : nest rtr j = some con) (h : ports con i = some ⟨v, k.opposite⟩)

inductive MutationDependency (rtr : α) (i : ID) : Kind → Prop
  | act  : (i ∈ (acts rtr).ids)                                    → MutationDependency rtr i k
  | prt  : (ports rtr i = some ⟨v, k⟩)                             → MutationDependency rtr i k
  | nest : (nest rtr j = some con) → (ports con i = some ⟨v, .in⟩) → MutationDependency rtr i .out

structure _root_.ReactorType.Wellformed (rtr : α) : Prop where
  uniqueInputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → (rtr[.prt][i] = some ⟨v, .in⟩) → (i ∈ rcn₁.deps .out) → (i ∉ rcn₂.deps .out)  
  overlapPrio  : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → (i₁ ≠ i₂) → (rcn₁.deps .out ∩ rcn₂.deps .out).Nonempty → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  impurePrio   : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → (i₁ ≠ i₂) → (¬rcn₁.Pure) → (¬rcn₂.Pure)                → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  mutationPrio : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → (i₁ ≠ i₂) → (rcn₁.Mutates) → (rcn₂.Mutates)            → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  normalDeps   : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (rcn.Normal)  → (d ∈ rcn.deps k) → (NormalDependency con d k) 
  mutationDeps : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (rcn.Mutates) → (d ∈ rcn.deps k) → (MutationDependency con d k) 
  acyclicDeps  : Dependency.Acyclic rtr

set_option hygiene false in
scoped macro "wf_nested_proof " name:ident : term => `(
  @fun
  | .nest _ => ($name ‹_› $ obj?_lift h ·)
  | .root   => ($name ‹_› <| obj?_lift_root h · |>.choose_spec)
)

theorem nested {rtr₁ : α} (wf : Wellformed rtr₁) (h : nest rtr₁ i = some rtr₂) : Wellformed rtr₂ where
  uniqueInputs h₁ h₂ h₃ h₄ := wf.uniqueInputs (obj?_lift h h₁) (obj?_lift h h₂) h₃ (obj?_lift h h₄) 
  overlapPrio              := wf_nested_proof overlapPrio
  impurePrio               := wf_nested_proof impurePrio
  mutationPrio             := wf_nested_proof mutationPrio
  normalDeps               := wf_nested_proof normalDeps
  mutationDeps             := wf_nested_proof mutationDeps
  acyclicDeps              := wf.acyclicDeps.nested h

end Wellformed
end ReactorType