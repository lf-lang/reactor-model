import ReactorModel.Objects.Reactor.ReactorType.Indexable

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

namespace Dependency

notation i₁ " <[" rtr "] " i₂ => Dependency rtr i₁ i₂

variable [Indexable α] [Indexable β] {rtr rtr₁ : α}

theorem nested (h : nest rtr₁ i = some rtr₂) (d : i₁ <[rtr₂] i₂) : i₁ <[rtr₁] i₂ := by
  induction d with
  | prio h₁          => exact prio (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | mutNorm h₁       => exact mutNorm (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | depOverlap h₁ h₂ => exact depOverlap (obj?_nested h h₁) (obj?_nested h h₂) ‹_› ‹_› ‹_›
  | mutNest h₁       => exact mutNest (obj?_nested' h h₁).choose_spec ‹_› ‹_› ‹_› ‹_›
  | trans _ _ d₁ d₂  => exact trans d₁ d₂

theorem lower [c : LawfulCoe α β] (d : i₁ <[rtr] i₂) : i₁ <[(rtr : β)] i₂ := by
  induction d with
  | prio h₁ h₂ h₃ =>
    exact prio (c.lower_obj?_some h₁) (c.lower_cpt?_eq_some .rcn h₂) (c.lower_cpt?_eq_some .rcn h₃) 
           ‹_› ‹_›
  | mutNorm h₁ h₂ h₃ => 
    exact mutNorm (c.lower_obj?_some h₁) (c.lower_cpt?_eq_some .rcn h₂)
          (c.lower_cpt?_eq_some .rcn h₃) ‹_› ‹_›
  | depOverlap h₁ h₂ => 
    exact depOverlap (c.lower_obj?_some h₁) (c.lower_obj?_some h₂) ‹_› ‹_› ‹_›
  | mutNest h₁ h₂ h₃ _ h₄ => 
    exact mutNest (c.lower_obj?_some h₁) (c.lower_cpt?_eq_some .rtr h₂)
          (c.lower_cpt?_eq_some .rcn h₃) ‹_› (c.lower_mem_cpt? .rcn h₄) 
  | trans _ _ d₁ d₂ => 
    exact trans d₁ d₂

open Equivalent in
theorem equiv (e : rtr₁ ≈ rtr₂) (d : j₁ <[rtr₂] j₂) : j₁ <[rtr₁] j₂ := by
  induction d with
  | prio h₁ h₂ h₃ => 
    -- TODO: The next 2 lines are a common pattern in the `updated` proofs. Perhaps create a 
    --       (unidirectional) derivative of `Equivalent.obj?_some_iff` that includes equivalence.
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    exact prio h₁' (rcns_eq e ▸ h₂) (rcns_eq e ▸ h₃) ‹_› ‹_›
  | mutNorm h₁ h₂ h₃ => 
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩  
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    exact mutNorm h₁' (rcns_eq e ▸ h₂) (rcns_eq e ▸ h₃) ‹_› ‹_›
  | depOverlap h₁ h₂ => 
    exact depOverlap (e.obj?_rcn_eq.symm ▸ h₁) (e.obj?_rcn_eq.symm ▸ h₂) ‹_› ‹_› ‹_›
  | mutNest h₁ h₂ h₃ _ h₄ => 
    have ⟨_, h₁'⟩ := e.obj?_some_iff.mpr ⟨_, h₁⟩  
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    have ⟨_, h₂'⟩ := cpt?_some_iff e (cpt := .rtr) |>.mpr ⟨_, h₂⟩
    have h₄' := mem_cpt?_iff (Equivalent.nest_equiv e h₂' h₂) (cpt := .rcn) |>.mpr h₄
    exact mutNest h₁' h₂' (rcns_eq e ▸ h₃) ‹_› h₄'
  | trans _ _ d₁ d₂ => 
    exact trans d₁ d₂

def Acyclic (rtr : α) : Prop :=
  ∀ i, ¬(i <[rtr] i)

namespace Acyclic

theorem nested (a : Acyclic rtr₁) (h : nest rtr₁ i = some rtr₂) : Acyclic rtr₂ :=
  fun i d => absurd (d.nested h) (a i)

theorem lift [LawfulCoe α β] (a : Acyclic (rtr : β)) : Acyclic rtr :=
  fun i d => absurd d.lower (a i) 
  
theorem equiv (e : rtr₁ ≈ rtr₂) (a : Acyclic rtr₁) : Acyclic rtr₂ :=
  fun i d => absurd (d.equiv e) (a i) 

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
  | act       : (i ∈ acts rtr) → ValidDependency rtr _ _ ⟨.act, i⟩ 
  | prt       : (i ∈ ports rtr dk) → ValidDependency rtr _ dk ⟨.prt k, i⟩  
  | nestedIn  : (nest rtr j = some con) → (i ∈ ports con .in) → 
                ValidDependency rtr _ .out ⟨.prt .in, i⟩
  | nestedOut : (nest rtr j = some con) → (i ∈ ports con .out) → 
                ValidDependency rtr .norm .in ⟨.prt .in, i⟩ 

set_option hygiene false in
scoped macro "lift_nested_proof " name:ident : term => `(
  fun hc hp => by
    have h := LawfulCoe.nest' (rtr := rtr) (β := β) ▸ hc 
    simp [Partial.map_val] at h
    obtain ⟨_, _, h⟩ := h
    subst h
    exact $(Lean.mkIdentFrom name $ `ValidDependency ++ name.getId) 
      (LawfulCoe.lift_cpt?_eq_some .rtr hc) (LawfulCoe.lift_mem_cpt? (.prt _) hp)
)

theorem ValidDependency.lift : (ValidDependency (rtr : β) rk dk d) → ValidDependency rtr rk dk d 
  | act h           => act $ LawfulCoe.lift_mem_cpt? .act h
  | prt h           => prt $ LawfulCoe.lift_mem_cpt? (.prt _) h
  | nestedIn hc hp  => (lift_nested_proof nestedIn) hc hp
  | nestedOut hc hp => (lift_nested_proof nestedOut) hc hp
    
end

variable [Indexable α] [Indexable β] {rtr rtr₁ : α}

set_option hygiene false in
scoped macro "equiv_nested_proof " name:ident : term => `(
  fun hc hp => 
    have e := Equivalent.obj?_rtr_equiv ‹_› h₁ h₂
    have ⟨_, hc'⟩ := Equivalent.cpt?_some_iff e (cpt := .rtr) |>.mp ⟨_, hc⟩ 
    have e := Equivalent.nest_equiv e hc hc'
    $(Lean.mkIdentFrom name $ `ValidDependency ++ name.getId) hc' 
    (Equivalent.mem_cpt?_iff e (cpt := .prt _) |>.mp hp)
)

open Equivalent in
theorem ValidDependency.equiv 
    (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][j] = some con₁) (h₂ : rtr₂[.rtr][j] = some con₂) : 
    (ValidDependency con₁ rk dk d) → ValidDependency con₂ rk dk d
  | act h           => act $ mem_cpt?_iff (obj?_rtr_equiv e h₁ h₂) (cpt := .act) |>.mp h
  | prt h           => prt $ mem_cpt?_iff (obj?_rtr_equiv e h₁ h₂) (cpt := .prt _) |>.mp h
  | nestedIn hc hp  => (equiv_nested_proof nestedIn) hc hp
  | nestedOut hc hp => (equiv_nested_proof nestedOut) hc hp

-- TODO: Refactor the `prio` conditions into one.
structure _root_.ReactorType.Wellformed (rtr : α) : Prop where
  unique_inputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → 
                  (i ∈ rtr[.prt .in]) → (⟨.prt .in, i⟩ ∈ rcn₁.deps .out) → 
                  (⟨.prt .in, i⟩ ∉ rcn₂.deps .out)  
  state_local   : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → 
                  (⟨.stv, s⟩ ∈ rcn.deps k) → (s ∈ state con)
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

set_option hygiene false in
scoped macro "wf_nested_proof " name:ident : term => `(
  @fun
  | (_ : ID) => ($name ‹_› $ obj?_nested h ·)
  | ⊤        => ($name ‹_› <| obj?_nested_root h · |>.choose_spec)
)

theorem nested (wf : Wellformed rtr₁) (h : nest rtr₁ i = some rtr₂) : Wellformed rtr₂ where
  state_local   := wf_nested_proof state_local
  overlap_prio  := wf_nested_proof overlap_prio
  hazards_prio  := wf_nested_proof hazards_prio
  mutation_prio := wf_nested_proof mutation_prio
  valid_deps    := wf_nested_proof valid_deps
  acyclic_deps  := wf.acyclic_deps.nested h
  unique_inputs h₁ h₂ _ h₄ := 
    wf.unique_inputs (obj?_nested h h₁) (obj?_nested h h₂) ‹_› (obj?_mem_nested h h₄)

set_option hygiene false in 
scoped macro "lift_prio_proof " name:ident : term => `(
  fun h₁ h₂ h₃ => 
    $(Lean.mkIdentFrom name $ `Wellformed ++ name.getId) ‹_› (LawfulCoe.lower_obj?_some h₁) 
    (LawfulCoe.lower_cpt?_eq_some .rcn h₂) (LawfulCoe.lower_cpt?_eq_some .rcn h₃)
)

theorem lift [c : LawfulCoe α β] (wf : Wellformed (rtr : β)) : Wellformed rtr where
  overlap_prio  := lift_prio_proof overlap_prio
  hazards_prio  := lift_prio_proof hazards_prio
  mutation_prio := lift_prio_proof mutation_prio
  acyclic_deps  := wf.acyclic_deps.lift (rtr := rtr)
  state_local h₁ h₂ h₃ := 
    c.lift_mem_cpt? .stv $ wf.state_local (c.lower_obj?_some h₁) (c.lower_cpt?_eq_some .rcn h₂) h₃ 
  valid_deps h₁ h₂ h₃ := 
    wf.valid_deps (c.lower_obj?_some h₁) (c.lower_cpt?_eq_some .rcn h₂) h₃ |>.lift
  unique_inputs h₁ h₂ _ h₃ := 
    wf.unique_inputs (c.lower_obj?_some h₁) (c.lower_obj?_some h₂) ‹_› (c.lower_mem_obj? h₃)

set_option hygiene false in
scoped macro "equiv_prio_proof " name:ident rtr₁:ident rtr₂:ident : term => `(
  fun h₁ h₂ h₃ => 
    have ⟨_, h₁'⟩ := Equivalent.obj?_some_iff ‹$rtr₁ ≈ $rtr₂› |>.mpr ⟨_, h₁⟩ 
    have e := Equivalent.obj?_rtr_equiv ‹_› h₁' h₁
    $(Lean.mkIdentFrom name $ `Wellformed ++ name.getId) 
      ‹_› h₁' (Equivalent.rcns_eq e ▸ h₂) (Equivalent.rcns_eq e ▸ h₃)
)

theorem equiv (e : rtr₁ ≈ rtr₂) (wf : Wellformed rtr₁) : Wellformed rtr₂ where
  overlap_prio  := equiv_prio_proof overlap_prio rtr₁ rtr₂
  hazards_prio  := equiv_prio_proof hazards_prio rtr₁ rtr₂
  mutation_prio := equiv_prio_proof mutation_prio rtr₁ rtr₂
  acyclic_deps  := wf.acyclic_deps.equiv e
  state_local h₁ h₂ h₃ :=
    have ⟨_, h₁'⟩ := Equivalent.obj?_some_iff e |>.mpr ⟨_, h₁⟩ 
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    have h₂' := Equivalent.rcns_eq e ▸ h₂
    Equivalent.mem_cpt?_iff e (cpt := .stv) |>.mp $ wf.state_local h₁' h₂' h₃
  valid_deps h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := Equivalent.obj?_some_iff e |>.mpr ⟨_, h₁⟩ 
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    have h₂' := Equivalent.rcns_eq e ▸ h₂
    wf.valid_deps h₁' h₂' h₃ |>.equiv ‹_› h₁' h₁
  unique_inputs h₁ h₂ _ h₃ := 
    have h₃' := Equivalent.mem_iff e |>.mpr h₃
    wf.unique_inputs (e.obj?_rcn_eq.symm ▸ h₁) (e.obj?_rcn_eq.symm ▸ h₂) ‹_› h₃'

end Wellformed
end ReactorType