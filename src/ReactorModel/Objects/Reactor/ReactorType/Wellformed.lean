import ReactorModel.Objects.Reactor.ReactorType.Equivalent

-- TODO: Are all of the theorems required to prove the `updated` theorems, theorems about 
--       `Reactor.Equivalent`?
--       Notable exception is `nested_rcns_eq`, but read the TODO on that theorem.
--       Thus, are all of the `updated` theorems actually provable from `Equivalent`.

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

notation i₁ " [" rtr "]> " i₂ => Dependency rtr i₁ i₂

variable [Indexable α] [Indexable β] {rtr rtr₁ : α}

instance : IsTrans ID (Dependency rtr) where 
  trans _ _ _ := trans 

theorem nested (h : nest rtr₁ i = some rtr₂) (d : i₁ [rtr₂]> i₂) : i₁ [rtr₁]> i₂ := by
  induction d with
  | prio h₁          => exact prio (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | mutNorm h₁       => exact mutNorm (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | depOverlap h₁ h₂ => exact depOverlap (obj?_nested h h₁) (obj?_nested h h₂) ‹_›
  | mutNest h₁       => exact mutNest (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | trans _ _ d₁ d₂  => exact trans d₁ d₂

theorem lower [c : LawfulCoe α β] (d : i₁ [rtr]> i₂) : i₁ [(rtr : β)]> i₂ := by
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

theorem updated {cmp f} (u : LawfulUpdate cmp i f rtr₁ rtr₂) (d : j₁ [rtr₂]> j₂) : j₁ [rtr₁]> j₂ := by
  induction d with
  | prio h₁ h₂ h₃ => 
    have ⟨_, h₁'⟩ := Equivalent.obj?_some_iff u.equiv |>.mpr ⟨_, h₁⟩  
    exact prio h₁' (u.nested_rcns_eq h₁' h₁ h₂) (u.nested_rcns_eq h₁' h₁ h₃) ‹_› ‹_›
  | mutNorm h₁ h₂ h₃ => 
    have ⟨_, h₁'⟩ := Equivalent.obj?_some_iff u.equiv |>.mpr ⟨_, h₁⟩  
    exact mutNorm h₁' (u.nested_rcns_eq h₁' h₁ h₂) (u.nested_rcns_eq h₁' h₁ h₃) ‹_› ‹_›
  | depOverlap h₁ h₂ => 
    exact depOverlap (u.equiv.rcns_eq.symm ▸ h₁) (u.equiv.rcns_eq.symm ▸ h₂) ‹_›
  | mutNest h₁ h₂ h₃ _ h₄ => 
    have ⟨_, h₁'⟩ := u.equiv.obj?_some_iff.mpr ⟨_, h₁⟩  
    have e := Equivalent.nested u.equiv h₁' h₁
    have ⟨_, h₂'⟩ := Equivalent.cmp?_some_iff e (cmp := .rtr) |>.mpr ⟨_, h₂⟩
    have h₄' := Equivalent.mem_cmp?_ids_iff (Equivalent.nest e h₂' h₂) (cmp := .rcn) |>.mpr h₄
    exact mutNest h₁' h₂' (u.nested_rcns_eq h₁' h₁ h₃) ‹_› h₄'
  | trans _ _ d₁ d₂ => 
    exact trans d₁ d₂

def Acyclic (rtr : α) : Prop :=
  ∀ i, ¬(i [rtr]> i)

namespace Acyclic

theorem nested (a : Acyclic rtr₁) (h : nest rtr₁ i = some rtr₂) : Acyclic rtr₂ :=
  fun i d => absurd (d.nested h) (a i)

theorem lift [LawfulCoe α β] (a : Acyclic (rtr : β)) : Acyclic rtr :=
  fun i d => absurd d.lower (a i) 
  
theorem updated {cmp f} (u : LawfulUpdate cmp i f rtr₁ rtr₂) (a : Acyclic rtr₁) : Acyclic rtr₂ :=
  fun i d => absurd (d.updated u) (a i) 

end Acyclic
end Dependency

namespace Wellformed

variable [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} in section

-- `ValidDependency rtr rk dk d` means that in reactor `rtr`, reactions of kind `rk` can have `d` as 
-- a valid dependency target of kind `dk`. For example `ValidDependency rtr .mut .out (.port .in i)` 
-- states that mutations can specify the input port identified by `i` as effect and 
-- `ValidDependency rtr .norm .in (.action i)` states that normal reactions can specify the action 
-- identified by `i` as source.
inductive ValidDependency (rtr : α) : Reaction.Kind → Kind → Reaction.Dependency → Prop
  | act       : (i ∈ (acts rtr).ids) → ValidDependency rtr _ _ (.action i)
  | prt       : (i ∈ (ports rtr dk).ids) → ValidDependency rtr _ dk (.port k i)
  | nestedIn  : (nest rtr j = some con) → (i ∈ (ports con .in).ids) → 
                ValidDependency rtr _ .out (.port .in i)
  | nestedOut : (nest rtr j = some con) → (i ∈ (ports con .out).ids) → 
                ValidDependency rtr .norm .in (.port .in i)

set_option hygiene false in
scoped macro "lift_nested_proof " name:ident : term => `(
  fun hc hp => by
    have h := LawfulCoe.nest' (rtr := rtr) (β := β) ▸ hc 
    simp [Partial.map_val] at h
    obtain ⟨_, _, h⟩ := h
    subst h
    exact $(Lean.mkIdentFrom name $ `ValidDependency ++ name.getId) 
      (LawfulCoe.lift_cmp?_eq_some .rtr hc) (LawfulCoe.lift_mem_cmp?_ids (.prt _) hp)
)

theorem ValidDependency.lift : (ValidDependency (rtr : β) rk dk d) → ValidDependency rtr rk dk d 
  | act h           => act $ LawfulCoe.lift_mem_cmp?_ids .act h
  | prt h           => prt $ LawfulCoe.lift_mem_cmp?_ids (.prt _) h
  | nestedIn hc hp  => (lift_nested_proof nestedIn) hc hp
  | nestedOut hc hp => (lift_nested_proof nestedOut) hc hp
    
end

variable [Indexable α] [Indexable β] {rtr rtr₁ : α}

set_option hygiene false in
scoped macro "updated_nested_proof " name:ident : term => `(
  fun hc hp => 
    have e := Equivalent.nested (LawfulUpdate.equiv ‹_›) h₁ h₂
    have ⟨_, hc'⟩ := Equivalent.cmp?_some_iff e (cmp := .rtr) |>.mp ⟨_, hc⟩ 
    have e := Equivalent.nest e hc hc'
    $(Lean.mkIdentFrom name $ `ValidDependency ++ name.getId) hc' 
    (Equivalent.mem_cmp?_ids_iff e (cmp := .prt _) |>.mp hp)
)

open Equivalent in
theorem ValidDependency.updated {cmp f} (u : LawfulUpdate cmp i f rtr₁ rtr₂)
    (h₁ : rtr₁[.rtr][j] = some con₁) (h₂ : rtr₂[.rtr][j] = some con₂) : 
    (ValidDependency con₁ rk dk d) → ValidDependency con₂ rk dk d
  | act h           => act $ mem_cmp?_ids_iff (nested u.equiv h₁ h₂) (cmp := .act) |>.mp h
  | prt h           => prt $ mem_cmp?_ids_iff (nested u.equiv h₁ h₂) (cmp := .prt _) |>.mp h
  | nestedIn hc hp  => (updated_nested_proof nestedIn) hc hp
  | nestedOut hc hp => (updated_nested_proof nestedOut) hc hp

-- TODO: Refactor the `prio` conditions into one.
structure _root_.ReactorType.Wellformed (rtr : α) : Prop where
  uniqueInputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → 
                 (i ∈ rtr[.prt .in].ids) → (.port .in i ∈ rcn₁.deps .out) → 
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
  validDeps    : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (d ∈ rcn.deps k) → 
                 (ValidDependency con rcn.kind k d) 
  acyclicDeps  : Dependency.Acyclic rtr

set_option hygiene false in
scoped macro "wf_nested_proof " name:ident : term => `(
  @fun
  | .nest _ => ($name ‹_› $ obj?_nested h ·)
  | .root   => ($name ‹_› <| obj?_nested_root h · |>.choose_spec)
)

theorem nested (wf : Wellformed rtr₁) (h : nest rtr₁ i = some rtr₂) : Wellformed rtr₂ where
  overlapPrio             := wf_nested_proof overlapPrio
  impurePrio              := wf_nested_proof impurePrio
  mutationPrio            := wf_nested_proof mutationPrio
  validDeps               := wf_nested_proof validDeps
  acyclicDeps             := wf.acyclicDeps.nested h
  uniqueInputs h₁ h₂ _ h₄ := 
    wf.uniqueInputs (obj?_nested h h₁) (obj?_nested h h₂) ‹_› (obj?_mem_ids_nested h h₄)

set_option hygiene false in 
scoped macro "lift_prio_proof " name:ident : term => `(
  fun h₁ h₂ h₃ => 
    $(Lean.mkIdentFrom name $ `Wellformed ++ name.getId) ‹_› (LawfulCoe.lower_obj?_some h₁) 
    (LawfulCoe.lower_cmp?_eq_some .rcn h₂) (LawfulCoe.lower_cmp?_eq_some .rcn h₃)
)

theorem lift [c : LawfulCoe α β] (wf : Wellformed (rtr : β)) : Wellformed rtr where
  overlapPrio  := lift_prio_proof overlapPrio
  impurePrio   := lift_prio_proof impurePrio
  mutationPrio := lift_prio_proof mutationPrio
  acyclicDeps  := wf.acyclicDeps.lift (rtr := rtr)
  validDeps h₁ h₂ h₃ := 
    wf.validDeps (c.lower_obj?_some h₁) (c.lower_cmp?_eq_some .rcn h₂) h₃ |>.lift
  uniqueInputs h₁ h₂ _ h₄ := 
    wf.uniqueInputs (c.lower_obj?_some h₁) (c.lower_obj?_some h₂) ‹_› (c.lower_mem_obj?_ids h₄)

set_option hygiene false in
scoped macro "updated_prio_proof " name:ident : term => `(
  fun h₁ h₂ h₃ => 
    have ⟨_, h₁'⟩ := Equivalent.obj?_some_iff u.equiv |>.mpr ⟨_, h₁⟩ 
    have e := Equivalent.nested u.equiv h₁' h₁
    $(Lean.mkIdentFrom name $ `Wellformed ++ name.getId) 
      ‹_› h₁' (Equivalent.nested_rcns_eq e h₂) (Equivalent.nested_rcns_eq e h₃)
)

theorem updated {cmp i f} (u : LawfulUpdate cmp i f rtr₁ rtr₂) (wf : Wellformed rtr₁) : 
    Wellformed rtr₂ where
  overlapPrio  := updated_prio_proof overlapPrio
  impurePrio   := updated_prio_proof impurePrio
  mutationPrio := updated_prio_proof mutationPrio
  acyclicDeps  := wf.acyclicDeps.updated u
  validDeps h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := Equivalent.obj?_some_iff u.equiv |>.mpr ⟨_, h₁⟩ 
    have e := Equivalent.nested u.equiv h₁' h₁
    have h₂' := Equivalent.nested_rcns_eq e h₂
    wf.validDeps h₁' h₂' h₃ |>.updated u h₁' h₁
  uniqueInputs h₁ h₂ _ h₃ := 
    have h₃' := Equivalent.mem_obj?_ids_iff u.equiv |>.mpr h₃
    wf.uniqueInputs (u.equiv.rcns_eq.symm ▸ h₁) (u.equiv.rcns_eq.symm ▸ h₂) ‹_› h₃'

end Wellformed
end ReactorType