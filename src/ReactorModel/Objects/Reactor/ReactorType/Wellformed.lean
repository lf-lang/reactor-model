import ReactorModel.Objects.Reactor.ReactorType.Indexable

namespace ReactorType

open Indexable

-- About the `↔`-condition in `prio`:  We want to establish a dependency between mutations with 
-- priorities as well normal reactions with priorities, but not between normal reactions and
-- mutations. Otherwise a normal reaction might take precedence over a mutation. Also the precedence
-- of mutations over normal reactions is handled by `mutNorm`, so this would potentially create a
-- redundancy.
--
-- Note: `Dependency _ i₁ i₂` means that in `i₁` must occur before `i₂`. 
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

def Acyclic (rtr : α) : Prop :=
  ∀ i, ¬(i [rtr]> i)

theorem Acyclic.nested (a : Acyclic rtr₁) (h : nest rtr₁ i = some rtr₂) : Acyclic rtr₂ :=
  fun i d => absurd (d.nested h) (a i)

theorem Acyclic.lift [LawfulCoe α β] (a : Acyclic (rtr : β)) : Acyclic rtr :=
  fun i d => absurd d.lower (a i) 
  
end Dependency

namespace Wellformed

variable [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} in section

-- `ValidDependent rtr rk dk d` means that in reactor `rtr`, reactions of kind `rk` can have `d` as 
-- a valid dependency target of kind `dk`. For example, `ValidTarget rtr .mut .out (.port .in i)` 
-- states that mutations can specify the input port identified by `i` as effect and 
-- `ValidTarget rtr .norm .in (.action i)` states that normal reactions can specify the action 
-- identified by `i` as source.
-- TODO: Come up with a better name for this type.
inductive ValidDependent (rtr : α) : Reaction.Kind → Kind → Reaction.Dependency → Prop
  | act       : (i ∈ (acts rtr).ids) → ValidDependent rtr _ _ (.action i)
  | prt       : (i ∈ (ports rtr dk).ids) → ValidDependent rtr _ dk (.port k i)
  | nestedIn  : (nest rtr j = some con) → (i ∈ (ports con .in).ids) → 
                ValidDependent rtr _ .out (.port .in i)
  | nestedOut : (nest rtr j = some con) → (i ∈ (ports con .out).ids) → 
               ValidDependent rtr .norm .in (.port .in i)

-- TODO: Factor out a lemma for `nestedIn` and `nestedOut`.
open ReactorType LawfulCoe in
theorem ValidDependent.lift : (ValidDependent (rtr : β) rk dk d) → ValidDependent rtr rk dk d 
  | act h => .act $ lift_mem_cmp?_ids .act h
  | prt h => .prt $ lift_mem_cmp?_ids (.prt _) h
  | nestedIn hc hp => by 
    have h := nest' (rtr := rtr) (β := β) ▸ hc 
    simp [Partial.map_val] at h
    obtain ⟨_, _, h⟩ := h
    subst h
    exact .nestedIn (lift_cmp?_eq_some .rtr hc) (lift_mem_cmp?_ids (.prt _) hp)
  | nestedOut hc hp => by 
    have h := nest' (rtr := rtr) (β := β) ▸ hc 
    simp [Partial.map_val] at h
    obtain ⟨_, _, h⟩ := h
    subst h
    exact .nestedOut (lift_cmp?_eq_some .rtr hc) (lift_mem_cmp?_ids (.prt _) hp)

end

variable [Indexable α] [Indexable β] {rtr rtr₁ : α}

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
  normalDeps   : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (rcn.Normal) → 
                 (d ∈ rcn.deps k) → (ValidDependent con .norm k d) 
  mutationDeps : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (rcn.Mutates) →
                 (d ∈ rcn.deps k) → (ValidDependent con .mut k d) 
  acyclicDeps  : Dependency.Acyclic rtr

set_option hygiene false in
scoped macro "wf_nested_proof " name:ident : term => `(
  @fun
  | .nest _ => ($name ‹_› $ obj?_nested h ·)
  | .root   => ($name ‹_› <| obj?_nested_root h · |>.choose_spec)
)

theorem nested (wf : Wellformed rtr₁) (h : nest rtr₁ i = some rtr₂) : Wellformed rtr₂ where
  overlapPrio              := wf_nested_proof overlapPrio
  impurePrio               := wf_nested_proof impurePrio
  mutationPrio             := wf_nested_proof mutationPrio
  normalDeps               := wf_nested_proof normalDeps
  mutationDeps             := wf_nested_proof mutationDeps
  acyclicDeps              := wf.acyclicDeps.nested h
  uniqueInputs h₁ h₂ h₃ h₄ := 
    -- TODO: If we separate `.rtr` from `Component`, turn this into a lemma.
    have h₄ := Partial.mem_ids_iff.mpr ⟨_, obj?_nested h (Partial.mem_ids_iff.mp h₄).choose_spec⟩ 
    wf.uniqueInputs (obj?_nested h h₁) (obj?_nested h h₂) h₃ h₄

theorem lift [c : LawfulCoe α β] (wf : Wellformed (rtr : β)) : Wellformed rtr where
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

theorem updated {cmp i f} (u : LawfulUpdate cmp i f rtr₁ rtr₂) (wf : Wellformed rtr₁) : Wellformed rtr₂ :=
  sorry
    /-
  wf.uniqueInputs h₁ h₂ _ h₄ :=
    rtr.wf.uniqueInputs (rtr.raw.update_ne_cmp_some_obj? h₁) (rtr.raw.update_ne_cmp_some_obj? h₂) 
    ‹_› sorry
  wf.overlapPrio h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := Reactor.Raw.update_rtr_some_obj? h₁
    have h₂ := Reactor.Raw.update_rtr_some_obj?_eq_cmp? .rcn h₁' h₁ h₂
    have h₃ := Reactor.Raw.update_rtr_some_obj?_eq_cmp? .rcn h₁' h₁ h₃
    rtr.wf.overlapPrio h₁' h₂ h₃
  wf.impurePrio h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := Reactor.Raw.update_rtr_some_obj? h₁
    have h₂ := Reactor.Raw.update_rtr_some_obj?_eq_cmp? .rcn h₁' h₁ h₂
    have h₃ := Reactor.Raw.update_rtr_some_obj?_eq_cmp? .rcn h₁' h₁ h₃
    rtr.wf.impurePrio h₁' h₂ h₃
  wf.mutationPrio h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := Reactor.Raw.update_rtr_some_obj? h₁
    have h₂ := Reactor.Raw.update_rtr_some_obj?_eq_cmp? .rcn h₁' h₁ h₂
    have h₃ := Reactor.Raw.update_rtr_some_obj?_eq_cmp? .rcn h₁' h₁ h₃
    rtr.wf.mutationPrio h₁' h₂ h₃
  wf.normalDeps h₁ h₂ h₃ h₄ :=
    have ⟨_, h₁'⟩ := Reactor.Raw.update_rtr_some_obj? h₁
    have h₂ := Reactor.Raw.update_rtr_some_obj?_eq_cmp? .rcn h₁' h₁ h₂
    have := rtr.wf.normalDeps h₁' h₂ h₃ h₄
    sorry 
    -- We need a lifting theorem:
    -- theorem NormalDependency.updated [Updatable α] {rtr : α}
    --    (h : rtr[.rtr][j] = some con) (hu : (update rtr cmp i f)[.rtr][j] = some con') 
    --    (hd : NormalDependency con k d) : NormalDependency con' k d := 
    --  sorry  
  wf.mutationDeps h₁ h₂ h₃ h₄ :=
    have ⟨_, h₁'⟩ := Reactor.Raw.update_rtr_some_obj? h₁
    have h₂ := Reactor.Raw.update_rtr_some_obj?_eq_cmp? .rcn h₁' h₁ h₂
    have := rtr.wf.mutationDeps h₁' h₂ h₃ h₄
    sorry 
    -- We need a lifting theorem:
    -- theorem MutationDependency.updated [Updatable α] {rtr : α}
    --    (h : rtr[.rtr][j] = some con) (hu : (update rtr cmp i f)[.rtr][j] = some con') 
    --    (hd : MutationDependency con k d) : MutationDependency con' k d := 
    --  sorry
  wf.acyclicDeps := 
    have := rtr.wf.acyclicDeps
    sorry
    -- We need a lifting theorem:
    -- theorem Dependency.Acyclic.updated [Updatable α] {rtr : α} (h : Acyclic rtr) : 
    --     Acyclic (update rtr cmp i f) :=
    --   sorry
-/

end Wellformed
end ReactorType