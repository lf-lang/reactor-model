import ReactorModel.Objects.Reactor.Dependency

namespace Reactor
namespace Raw
namespace Wellformed

open Lean in set_option hygiene false in
macro "def_wellformedness" ns:ident : command => 
  let namespaced name := mkIdentFrom ns $ ns.getId ++ name
  let reactorType := if ns.getId = `Reactor then ns else mkIdentFrom ns $ `Reactor ++ ns.getId
  `(
    inductive NormalDependency (rtr : $reactorType) (i : ID) (k : Kind) : Prop
      | act  (h : i ∈ rtr.acts.ids)
      | prt  (h : rtr.ports i = some ⟨v, k⟩)
      | nest (c : rtr.nest j = some con) (h : con.ports i = some ⟨v, k.opposite⟩)

    inductive MutationDependency (rtr : $reactorType) (i : ID) : Kind → Prop
      | act  : (i ∈ rtr.acts.ids) → MutationDependency rtr i k
      | prt  : (rtr.ports i = some ⟨v, k⟩) → MutationDependency rtr i k
      | nest : (rtr.nest j = some con) → (con.ports i = some ⟨v, .in⟩) → MutationDependency rtr i .out

    structure $(mkIdentFrom reactorType $ `_root_ ++ reactorType.getId ++ `Wellformed) (rtr : $reactorType) : Prop where
      uniqueInputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → (rtr[.prt][i] = some ⟨v, .in⟩) → (i ∈ rcn₁.deps .out) → (i ∉ rcn₂.deps .out)  
      overlapPrio  : (rtr[.rtr][i] = some con) → (con.rcns i₁ = some rcn₁) → (con.rcns i₂ = some rcn₂) → (i₁ ≠ i₂) → (rcn₁.deps .out ∩ rcn₂.deps .out).Nonempty → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
      impurePrio   : (rtr[.rtr][i] = some con) → (con.rcns i₁ = some rcn₁) → (con.rcns i₂ = some rcn₂) → (i₁ ≠ i₂) → (¬rcn₁.Pure) → (¬rcn₂.Pure)                → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
      mutationPrio : (rtr[.rtr][i] = some con) → (con.rcns i₁ = some rcn₁) → (con.rcns i₂ = some rcn₂) → (i₁ ≠ i₂) → (rcn₁.Mutates) → (rcn₂.Mutates)            → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
      normalDeps   : (rtr[.rtr][i] = some con) → (con.rcns j = some rcn) → (rcn.Normal)  → (d ∈ rcn.deps k) → (NormalDependency con d k) 
      mutationDeps : (rtr[.rtr][i] = some con) → (con.rcns j = some rcn) → (rcn.Mutates) → (d ∈ rcn.deps k) → (MutationDependency con d k) 
      acyclicDeps  : $(namespaced `Dependency.Acyclic) rtr
  )

def_wellformedness Raw

open Lean in set_option hygiene false in
scoped macro "wf_nested_proof " name:ident : term => `(
  @fun
  | .nest i => ($(mkIdentFrom name $ `wf ++ name.getId) $ obj?_lift h ·)
  | .root   => ($(mkIdentFrom name $ `wf ++ name.getId) <| obj?_lift_root h · |>.choose_spec)
)

theorem nested (wf : Wellformed rtr₁) (h : rtr₁.nest i = some rtr₂) : Wellformed rtr₂ where
  uniqueInputs h₁ h₂ h₃ h₄ := wf.uniqueInputs (obj?_lift h h₁) (obj?_lift h h₂) h₃ (obj?_lift h h₄) 
  overlapPrio              := wf_nested_proof overlapPrio
  impurePrio               := wf_nested_proof impurePrio
  mutationPrio             := wf_nested_proof mutationPrio
  normalDeps               := wf_nested_proof normalDeps
  mutationDeps             := wf_nested_proof mutationDeps
  acyclicDeps              := wf.acyclicDeps.nested h

end Wellformed
end Raw
end Reactor