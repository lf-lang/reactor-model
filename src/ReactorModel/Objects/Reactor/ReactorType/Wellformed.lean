import ReactorModel.Objects.Reactor.ReactorType.Indexable

namespace ReactorType

open Indexable

-- About the `↔`-condition in `prio`:  We want to establish a dependency between mutations with 
-- priorities as well normal reactions with priorities, but not between normal reactions and
-- mutations. Otherwise a normal reaction might take precedence over a mutation. Also the precedence
-- of mutations over normal reactions is handled by `mutNorm`, so this would potentially create a
-- redundancy.
inductive Dependency [Indexable α] (rtr : α) : ID → ID → Prop
  | prio :
    (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → 
    (rcn₁.Mutates ↔ rcn₂.Mutates) → (rcn₁.prio > rcn₂.prio) → Dependency rtr i₁ i₂
  | mutNorm : 
    (rtr[.rtr][i] = some con) → (rcns con iₘ = some m) → (rcns con iₙ = some n) → (m.Mutates) → 
    (n.Normal) → Dependency rtr iₘ iₙ
  | depOverlap :
    (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) →
    (rcn₁.deps .out ∩ rcn₂.deps .in).Nonempty → Dependency rtr i₁ i₂
  | mutNest :
    (rtr[.rtr][i] = some rtr₁) → (nest rtr₁ j = some rtr₂) → (rcns rtr₁ iₘ = some m) → (m.Mutates) →
    (iᵣ ∈ (rcns rtr₂).ids) → Dependency rtr iₘ iᵣ
  | trans : 
    Dependency rtr i₁ i₂ → Dependency rtr i₂ i₃ → Dependency rtr i₁ i₃

namespace Dependency

theorem nested [Indexable α] {rtr₁ : α} 
    (h : nest rtr₁ i = some rtr₂) (d : Dependency rtr₂ i₁ i₂) : Dependency rtr₁ i₁ i₂ := by
  induction d with
  | prio h₁          => exact prio (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | mutNorm h₁       => exact mutNorm (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | depOverlap h₁ h₂ => exact depOverlap (obj?_nested h h₁) (obj?_nested h h₂) ‹_›
  | mutNest h₁       => exact mutNest (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | trans _ _ d₁ d₂  => exact trans d₁ d₂

theorem lower [Indexable α] [Indexable β] [c : LawfulCoe α β] {rtr : α} (d : Dependency rtr i₁ i₂) :
    Dependency (rtr : β) i₁ i₂ := by
  induction d with
  | prio h₁ h₂ h₃ =>
     exact prio (c.lower_obj?_some h₁) (c.lower_cmp?_eq_some .rcn h₂) (c.lower_cmp?_eq_some .rcn h₃) 
           ‹_› ‹_›
  | mutNorm h₁ h₂ h₃ => 
    exact mutNorm (c.lower_obj?_some h₁) (c.lower_cmp?_eq_some .rcn h₂)
          (c.lower_cmp?_eq_some .rcn h₃) ‹_› ‹_›
  | depOverlap h₁ h₂ => 
    exact depOverlap (c.lower_obj?_some h₁) (c.lower_obj?_some h₂) ‹_›
  | mutNest h₁ h₂ h₃ _ h₄ => 
    exact mutNest (c.lower_obj?_some h₁) (c.lower_cmp?_eq_some .rtr h₂)
          (c.lower_cmp?_eq_some .rcn h₃) ‹_› (c.lower_mem_cmp?_ids .rcn h₄) 
  | trans _ _ d₁ d₂ => 
    exact trans d₁ d₂

def Acyclic [Indexable α] (rtr : α) : Prop :=
  ∀ i, ¬Dependency rtr i i 

theorem Acyclic.nested [Indexable α] {rtr₁ : α} (a : Acyclic rtr₁) (h : nest rtr₁ i = some rtr₂) :  
    Acyclic rtr₂ :=
  fun i d => absurd (d.nested h) (a i)

theorem Acyclic.lift [Indexable α] [Indexable β] [LawfulCoe α β] {rtr : α} (a : Acyclic (rtr : β)) : 
    Acyclic rtr :=
  fun i d => absurd d.lower (a i) 
  
end Dependency

namespace Wellformed

inductive NormalDependency [ReactorType α] (rtr : α) (k : Kind) : Reaction.Dependency → Prop
  | act  : (i ∈ (acts rtr).ids) → NormalDependency rtr k (.action i)
  | prt  : (i ∈ (ports rtr k).ids) → NormalDependency rtr k (.port k i)
  | nest : (nest rtr j = some con) → (i ∈ (ports con k.opposite).ids) → 
           NormalDependency rtr k (.port k i)

inductive MutationDependency [ReactorType α] (rtr : α) : Kind → Reaction.Dependency → Prop
  | act  : (i ∈ (acts rtr).ids) → MutationDependency rtr k (.action i)
  | prt  : (i ∈ (ports rtr k).ids) → MutationDependency rtr k (.port k i)
  | nest : (nest rtr j = some con) → (i ∈ (ports con .in).ids) → 
           MutationDependency rtr .out (.port .in i)

set_option hygiene false in
scoped macro "norm_and_mut_lift_proof" : term => `(
  open ReactorType LawfulCoe in
  fun
  | act h => .act $ lift_mem_cmp?_ids .act h
  | prt h => .prt $ lift_mem_cmp?_ids (.prt _) h
  | nest hc hp => by 
    have h := nest' (rtr := rtr) (β := β) ▸ hc 
    simp [Partial.map_val] at h
    obtain ⟨_, _, h⟩ := h
    subst h
    exact .nest (lift_cmp?_eq_some .rtr hc) (lift_mem_cmp?_ids (.prt _) hp)
)

theorem NormalDependency.lift [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} : 
    (NormalDependency (rtr : β) i k) → NormalDependency rtr i k :=
  norm_and_mut_lift_proof

theorem MutationDependency.lift [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} :
    (MutationDependency (rtr : β) i k) → MutationDependency rtr i k :=
  norm_and_mut_lift_proof

structure _root_.ReactorType.Wellformed [Indexable α] (rtr : α) : Prop where
  uniqueInputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → 
                 (i ∈ rtr[.inp].ids) → (.port .in i ∈ rcn₁.deps .out) → 
                 (.port .in i ∉ rcn₂.deps .out)  
  overlapPrio  : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → 
                 (i₁ ≠ i₂) → (rcn₁.deps .out ∩ rcn₂.deps .out).Nonempty → 
                 (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  impurePrio   : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → 
                 (i₁ ≠ i₂) → (¬rcn₁.Pure) → (¬rcn₂.Pure) → 
                 (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  mutationPrio : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → 
                 (i₁ ≠ i₂) → (rcn₁.Mutates) → (rcn₂.Mutates) →
                 (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  normalDeps   : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (rcn.Normal) → 
                 (d ∈ rcn.deps k) → (NormalDependency con k d) 
  mutationDeps : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (rcn.Mutates) →
                 (d ∈ rcn.deps k) → (MutationDependency con k d) 
  acyclicDeps  : Dependency.Acyclic rtr

set_option hygiene false in
scoped macro "wf_nested_proof " name:ident : term => `(
  @fun
  | .nest _ => ($name ‹_› $ obj?_nested h ·)
  | .root   => ($name ‹_› <| obj?_nested_root h · |>.choose_spec)
)

theorem nested [Indexable α] {rtr₁ : α} 
    (wf : Wellformed rtr₁) (h : nest rtr₁ i = some rtr₂) : Wellformed rtr₂ where
  overlapPrio              := wf_nested_proof overlapPrio
  impurePrio               := wf_nested_proof impurePrio
  mutationPrio             := wf_nested_proof mutationPrio
  normalDeps               := wf_nested_proof normalDeps
  mutationDeps             := wf_nested_proof mutationDeps
  acyclicDeps              := wf.acyclicDeps.nested h
  uniqueInputs h₁ h₂ h₃ h₄ := 
    -- TODO: If we separate `.rtr` frrom `Component`, turn this into a lemma.
    have h₄ := Partial.mem_ids_iff.mpr ⟨_, obj?_nested h (Partial.mem_ids_iff.mp h₄).choose_spec⟩ 
    wf.uniqueInputs (obj?_nested h h₁) (obj?_nested h h₂) h₃ h₄

theorem lift [Indexable α] [Indexable β] [c : LawfulCoe α β] {rtr : α} (wf : Wellformed (rtr : β)) : 
    Wellformed rtr where
  uniqueInputs h₁ h₂ h₃ h₄ := 
    wf.uniqueInputs (c.lower_obj?_some h₁) (c.lower_obj?_some h₂) h₃ (c.lower_mem_obj?_ids h₄)
  overlapPrio h₁ h₂ h₃ := 
    wf.overlapPrio (c.lower_obj?_some h₁) (c.lower_cmp?_eq_some .rcn h₂) 
    (c.lower_cmp?_eq_some .rcn h₃)
  impurePrio h₁ h₂ h₃ := 
    wf.impurePrio (c.lower_obj?_some h₁) (c.lower_cmp?_eq_some .rcn h₂) 
    (c.lower_cmp?_eq_some .rcn h₃)
  mutationPrio h₁ h₂ h₃ := 
    wf.mutationPrio (c.lower_obj?_some h₁) (c.lower_cmp?_eq_some .rcn h₂) 
    (c.lower_cmp?_eq_some .rcn h₃)
  normalDeps h₁ h₂ h₃ h₄ := 
    wf.normalDeps (c.lower_obj?_some h₁) (c.lower_cmp?_eq_some .rcn h₂) h₃ h₄ |>.lift
  mutationDeps h₁ h₂ h₃ h₄ := 
    wf.mutationDeps (c.lower_obj?_some h₁) (c.lower_cmp?_eq_some .rcn h₂) h₃ h₄ |>.lift
  acyclicDeps := 
    wf.acyclicDeps.lift (rtr := rtr)

end Wellformed
end ReactorType