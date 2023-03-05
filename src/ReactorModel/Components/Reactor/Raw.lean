import ReactorModel.Components.Reaction

open Classical     

namespace Reactor

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Component
  | rtr -- Nested reactors
  | rcn -- Reactions
  | prt -- Ports
  | act -- Actions
  | stv -- State variables

abbrev Component.idType : Component → Type _
  | rtr => RootedID
  | _   => ID

instance {cmp : Component} : Coe ID cmp.idType where
  coe i :=
    match cmp with
    | .rtr => .nest i
    | .rcn | .prt | .act | .stv => i

protected inductive Core 
  | mk 
    (ports : ID ⇀ Port)
    (acts :  ID ⇀ Time.Tag ⇀ Value)
    (state : ID ⇀ Value)
    (rcns :  ID ⇀ Reaction)
    (nest :  ID → Option Reactor.Core)

namespace Core

-- These definitions give us the projections that would usually be generated for a structure.
protected def ports : Reactor.Core → ID ⇀ Port             | mk p _ _ _ _ => p
protected def acts :  Reactor.Core → ID ⇀ Time.Tag ⇀ Value | mk _ a _ _ _ => a
protected def state : Reactor.Core → ID ⇀ Value            | mk _ _ s _ _ => s 
protected def rcns :  Reactor.Core → ID ⇀ Reaction         | mk _ _ _ r _ => r
protected def nest :  Reactor.Core → ID ⇀ Reactor.Core     | mk _ _ _ _ n => n

theorem ext_iff {rtr₁ rtr₂ : Reactor.Core} : 
    rtr₁ = rtr₂ ↔ 
    rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts ∧ rtr₁.state = rtr₂.state ∧ 
    rtr₁.rcns = rtr₂.rcns ∧ rtr₁.nest  = rtr₂.nest := by
  constructor
  all_goals
    intro _
    cases rtr₁
    cases rtr₂
    simp_all [Core.ports, Core.state, Core.rcns, Core.acts, Core.nest]

open Lean in set_option hygiene false in
macro "def_lineage_type " ns:ident : command => 
  let namespaced name := mkIdentFrom ns $ ns.getId ++ name
  let reactorType := if ns.getId = `Reactor then ns else mkIdentFrom ns $ `Reactor ++ ns.getId
  let lineageType := namespaced `Lineage
  `(
    protected abbrev componentType : Component → Type _
      | .rtr => $reactorType
      | .rcn => Reaction
      | .prt => Port
      | .act => Time.Tag ⇀ Value
      | .stv => Value

    protected abbrev cmp? : (cmp : Component) → $reactorType → ID ⇀ $(namespaced `componentType) cmp
      | .rtr => $(namespaced `nest)
      | .rcn => $(namespaced `rcns)
      | .prt => $(namespaced `ports)
      | .act => $(namespaced `acts)
      | .stv => $(namespaced `state)

    protected inductive Lineage (cmp : Component) (i : ID) : $reactorType → Type _
      | final : i ∈ (rtr.cmp? cmp).ids → $lineageType cmp i rtr
      | nest : (rtr₁.nest j = some rtr₂) → ($lineageType cmp i rtr₂) → $lineageType cmp i rtr₁
  )

def_lineage_type Core -- defines `componentType`, `cmp?` and `Lineage`

end Core

protected structure Raw where
  core : Reactor.Core
  uniqueIDs : ∀ {cmp i} (l₁ l₂ : Core.Lineage cmp i core), l₁ = l₂ 

namespace Raw

protected def ports : Reactor.Raw → ID ⇀ Port             := (·.core.ports)
protected def acts  : Reactor.Raw → ID ⇀ Time.Tag ⇀ Value := (·.core.acts)
protected def state : Reactor.Raw → ID ⇀ Value            := (·.core.state)
protected def rcns  : Reactor.Raw → ID ⇀ Reaction         := (·.core.rcns)

protected def nest (rtr : Reactor.Raw) : ID ⇀ Reactor.Raw :=
  rtr.core.nest.attach.map fun ⟨core, h⟩ => {
    core := core
    uniqueIDs := by
      intro _ _ l₁ l₂
      injection rtr.uniqueIDs (.nest h.choose_spec l₁) (.nest h.choose_spec l₂)
  }

open Lean in set_option hygiene false in
macro "def_lineage_accessors " ns:ident : command => 
  let namespaced name := mkIdentFrom ns $ ns.getId ++ name
  let reactorType := if ns.getId = `Reactor then ns else mkIdentFrom ns $ `Reactor ++ ns.getId
  let lineageType := mkIdentFrom reactorType $ reactorType.getId ++ `Lineage
  `(
    def Lineage.container {cmp} : $lineageType cmp i rtr → Identified $reactorType 
    | nest _ (nest h l)              => container (nest h l)
    | nest (rtr₁ := con) (j := j) .. => { id := j, obj := con }
    | _                              => { id := ⊤, obj := rtr }

    protected noncomputable def con? (rtr : $reactorType ) (cmp : Component) (i : ID) : 
        Option (Identified $reactorType) := 
      if l : Nonempty ($lineageType cmp i rtr) then l.some.container else none

    protected noncomputable def obj? (rtr : $reactorType) : 
        (cmp : Component) → cmp.idType ⇀ $(namespaced `componentType) cmp
      | .rtr, .nest i => rtr.con? .rtr i >>= (·.obj.cmp? .rtr i)
      | .rtr, ⊤       => rtr
      | .rcn,  i      => rtr.con? .rcn i >>= (·.obj.cmp? .rcn i)
      | .prt,  i      => rtr.con? .prt i >>= (·.obj.cmp? .prt i)
      | .act,  i      => rtr.con? .act i >>= (·.obj.cmp? .act i)
      | .stv,  i      => rtr.con? .stv i >>= (·.obj.cmp? .stv i)
  )

def_lineage_type Raw      -- defines `componentType`, `cmp?` and `Lineage`
def_lineage_accessors Raw -- defines `Lineage.container`, `con?` and `obj?`

scoped notation rtr "[" cmp "][" i "]" => Reactor.Raw.obj? rtr cmp i

theorem obj?_nest {cmp o} {j : ID} : 
    (σ.nest i = some rtr) → (rtr[cmp][j] = some o) → σ[cmp][j] = some o := by
  sorry

theorem obj?_nest_root_rtr : 
    (σ.nest i = some rtr) → (rtr[.rtr][⊤] = some o) → ∃ j, σ[.rtr][j] = some o := by
  sorry

-- About the ↔-condition in prio: 
-- We want to establish a dependency between mutations with priorities 
-- as well normal reactions with priorities, but not between normal reactions
-- and mutations. Otherwise a normal reaction might take precedence over
-- a mutation. Also the precedence of mutations over normal reactions is
-- handled by mutNorm - so this would potentially just create a redundancy.
inductive Dependency (σ : Reactor.Raw) : ID → ID → Prop
  | prio :
    (σ.con? .rcn i₁ = σ.con? .rcn i₂) → (σ[.rcn][i₁] = some rcn₁) → (σ[.rcn][i₂] = some rcn₂) →
    (rcn₁.Mutates ↔ rcn₂.Mutates) → (rcn₁.prio > rcn₂.prio) → Dependency σ i₁ i₂
  | mutNorm : 
    (σ.con? .rcn iₘ = σ.con? .rcn iₙ) → (σ[.rcn][iₘ] = some m) → (σ[.rcn][iₙ] = some n) →
    (m.Mutates) → (n.Normal) → Dependency σ iₘ iₙ
  | depOverlap :
    (σ[.rcn][i₁] = some rcn₁) → (σ[.rcn][i₂] = some rcn₂) →
    (rcn₁.deps .out ∩ rcn₂.deps .in).Nonempty → Dependency σ i₁ i₂
  | mutNest :
    (σ[.rcn][iₘ] = some m) → (m.Mutates) → (σ.con? .rcn iₘ = some rtr₁) →
    (rtr₁.obj.nest j = some rtr₂) → (iᵣ ∈ rtr₂.rcns.ids) → Dependency σ iₘ iᵣ
  | trans : 
    Dependency σ i₁ i₂ → Dependency σ i₂ i₃ → Dependency σ i₁ i₃

def Dependency.Acyclic (rtr : Reactor.Raw) : Prop :=
  ∀ i, ¬Dependency rtr i i 

theorem Dependency.Acyclic.nested (a : Acyclic rtr₁) (h : rtr₁.nest i = some rtr₂) : Acyclic rtr₂ :=
  sorry

namespace Wellformed

inductive NormalDependency (rtr : Reactor.Raw) (i : ID) (k : Kind) : Prop
  | act  (h : i ∈ rtr.acts.ids)
  | prt  (h : rtr.ports i = some ⟨v, k⟩)
  | nest (c : rtr.nest j = some con) (h : con.ports i = some ⟨v, k.opposite⟩)

inductive MutationDependency (rtr : Reactor.Raw) (i : ID) : Kind → Prop
  | act  : (i ∈ rtr.acts.ids) → MutationDependency rtr i k
  | prt  : (rtr.ports i = some ⟨v, k⟩) → MutationDependency rtr i k
  | nest : (rtr.nest j = some con) → (con.ports i = some ⟨v, .in⟩) → MutationDependency rtr i .out

structure _root_.Reactor.Raw.Wellformed (rtr : Reactor.Raw) : Prop where
  overlapPrio  : (rtr[.rtr][i] = some con) → (con.rcns i₁ = some rcn₁) → (con.rcns i₂ = some rcn₂) → (i₁ ≠ i₂) → (rcn₁.deps .out ∩ rcn₂.deps .out).Nonempty → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  impurePrio   : (rtr[.rtr][i] = some con) → (con.rcns i₁ = some rcn₁) → (con.rcns i₂ = some rcn₂) → (i₁ ≠ i₂) → (¬rcn₁.Pure) → (¬rcn₂.Pure)                → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  mutationPrio : (rtr[.rtr][i] = some con) → (con.rcns i₁ = some rcn₁) → (con.rcns i₂ = some rcn₂) → (i₁ ≠ i₂) → (rcn₁.Mutates) → (rcn₂.Mutates)            → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  normalDeps   : (rtr[.rtr][i] = some con) → (con.rcns j = some rcn) → (rcn.Normal)  → (d ∈ rcn.deps k) → (NormalDependency con d k) 
  mutationDeps : (rtr[.rtr][i] = some con) → (con.rcns j = some rcn) → (rcn.Mutates) → (d ∈ rcn.deps k) → (MutationDependency con d k) 
  uniqueInputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → (rtr[.prt][i] = some ⟨v, .in⟩) → (i ∈ rcn₁.deps .out) → (i ∉ rcn₂.deps .out)  
  acyclic      : Dependency.Acyclic rtr

open Lean in set_option hygiene false in
scoped macro "wf_nested_proof " name:ident : term => `(
  @fun
  | .nest i => ($(mkIdentFrom name $ `wf ++ name.getId) $ obj?_nest h ·)
  | .root   => ($(mkIdentFrom name $ `wf ++ name.getId) <| obj?_nest_root_rtr h · |>.choose_spec)
)

theorem nested (wf : Wellformed rtr₁) (h : rtr₁.nest i = some rtr₂) : Wellformed rtr₂ where
  overlapPrio              := wf_nested_proof overlapPrio
  impurePrio               := wf_nested_proof impurePrio
  mutationPrio             := wf_nested_proof mutationPrio
  normalDeps               := wf_nested_proof normalDeps
  mutationDeps             := wf_nested_proof mutationDeps
  uniqueInputs h₁ h₂ h₃ h₄ := wf.uniqueInputs (obj?_nest h h₁) (obj?_nest h h₂) h₃ (obj?_nest h h₄) 
  acyclic                  := wf.acyclic.nested h

end Wellformed

end Raw

structure _root_.Reactor where
  raw : Reactor.Raw
  wf  : raw.Wellformed

def ports : Reactor → ID ⇀ Port             := (·.raw.ports)
def acts  : Reactor → ID ⇀ Time.Tag ⇀ Value := (·.raw.acts)
def state : Reactor → ID ⇀ Value            := (·.raw.state)
def rcns  : Reactor → ID ⇀ Reaction         := (·.raw.rcns)

def nest (rtr : Reactor) : ID ⇀ Reactor :=
  rtr.raw.nest.attach.map fun ⟨raw, h⟩ => { raw := raw, wf := rtr.wf.nested h.choose_spec }

def_lineage_type Reactor      -- defines `componentType`, `cmp?` and `Lineage`
def_lineage_accessors Reactor -- defines `Lineage.container`, `con?` and `obj?`

end Reactor
