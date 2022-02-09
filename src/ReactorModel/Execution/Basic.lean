import ReactorModel.Execution.Context

variable {ι υ} [Value υ]

-- TODO: You're only ever using (σ, ctx) together. Create some structure that bundles them.

-- TODO: Come up with something nicer.
structure Reactor.eqWithClearedPorts (σ₁ σ₂ : Reactor ι υ) where
  otherCmpsEq : ∀ {cmp}, cmp ≠ Cmp.prt → cmp.accessor σ₁ = cmp.accessor σ₂
  priosEq : σ₁.prios = σ₂.prios
  rolesEq : σ₁.roles = σ₂.roles
  samePortIDs : ∀ i, σ₁.containsID i Cmp.prt ↔ σ₂.containsID i Cmp.prt
  clearedIDs : ∀ i, σ₂.containsID i Cmp.prt → σ₂ *[Cmp.prt, i]= ⊥

lemma Reactor.eqWithClearedPortsUnique {σ σ₁ σ₂ : Reactor ι υ} :
 Reactor.eqWithClearedPorts σ σ₁ → Reactor.eqWithClearedPorts σ σ₂ → 
 σ₁ = σ₂ := sorry
 
namespace Execution

inductive ChangeStep (g : Time.Tag) (σ₁ : Reactor ι υ) : Reactor ι υ → Change ι υ → Prop 
  | port (σ₂) {i v} : (σ₁ -[Cmp.prt, i := v]→ σ₂) → ChangeStep g σ₁ σ₂ (Change.port i v) -- Port propagation isn't necessary/possible, because we're using relay reactions. 
  | state (σ₂) {i v} : (σ₁ -[Cmp.stv, i := v]→ σ₂) → ChangeStep g σ₁ σ₂ (Change.state i v)
  | action (σ₂) {i} {t : Time} {tg : Time.Tag} {v : υ} {a : Time.Tag ▸ υ} : 
    (σ₁.acts i = a) → 
    (t.after g = tg) → 
    (σ₁ -[Cmp.act, i := a.update tg v]→ σ₂) → 
    ChangeStep g σ₁ σ₂ (Change.action i t v)
  -- Mutations are (temporarily) no-ops:
  | connect {i₁ i₂} : ChangeStep g σ₁ σ₁ (Change.connect i₁ i₂)
  | disconnect {i₁ i₂} : ChangeStep g σ₁ σ₁ (Change.disconnect i₁ i₂)
  | create {rtr i} : ChangeStep g σ₁ σ₁ (Change.create rtr i)
  | delete {i} : ChangeStep g σ₁ σ₁ (Change.delete i)

notation σ₁:max " -[" c ", " g "]→ " σ₂:max => ChangeStep g σ₁ σ₂ c

inductive ChangeListStep (g : Time.Tag) : Reactor ι υ → Reactor ι υ → List (Change ι υ) → Prop
  | nil (σ₁) : ChangeListStep g σ₁ σ₁ []
  | cons {σ₁ σ₂ σ₃ change rest} : (σ₁ -[change, g]→ σ₂) → (ChangeListStep g σ₂ σ₃ rest) → ChangeListStep g σ₁ σ₃ (change::rest)

notation σ₁:max " -[" cs ", " g "]→* " σ₂:max => ChangeListStep g σ₁ σ₂ cs

-- We separate the execution into two parts, the instantaneous execution which controlls
-- how reactors execute at a given instant, and the timed execution, which includes the
-- passing of time
inductive InstStep (σ : Reactor ι υ) (ctx : Context ι) : Reactor ι υ → Context ι → Prop 
  | execReaction {rcn : Reaction ι υ} {i σ'} : 
    (σ.rcns i = rcn) →
    (σ.predecessors i ⊆ ctx.currentExecutedRcns) →
    (i ∉ ctx.currentExecutedRcns) →
    (rcn.triggersOn $ σ.inputForRcn rcn ctx.time) →
    (σ -[rcn $ σ.inputForRcn rcn ctx.time, ctx.time]→* σ') →
    InstStep σ ctx σ' (ctx.addCurrentExecuted i)
  | skipReaction {rcn : Reaction ι υ} {i} :
    (σ.rcns i = rcn) →
    (σ.predecessors i ⊆ ctx.currentExecutedRcns) →
    (i ∉ ctx.currentExecutedRcns) →
    (¬(rcn.triggersOn $ σ.inputForRcn rcn ctx.time)) →
    InstStep σ ctx σ (ctx.addCurrentExecuted i)

notation "(" σ₁ ", " ctx₁ ") ⇓ᵢ (" σ₂ ", " ctx₂ ")" => InstStep σ₁ ctx₁ σ₂ ctx₂

-- An execution at an instant is a series of steps,
-- which we model with the transitive closure.
inductive InstExecution : Reactor ι υ → Context ι → Reactor ι υ → Context ι → Prop 
  | single {σ₁ σ₂ ctx₁ ctx₂} : (σ₁, ctx₁) ⇓ᵢ (σ₂, ctx₂) → InstExecution σ₁ ctx₁ σ₂ ctx₂
  | trans {σ₁ σ₂ σ₃ ctx₁ ctx₂ ctx₃} : (σ₁, ctx₁) ⇓ᵢ (σ₂, ctx₂) → InstExecution σ₂ ctx₂ σ₃ ctx₃ → InstExecution σ₁ ctx₁ σ₃ ctx₃

notation "(" σ₁ ", " ctx₁ ") ⇓ᵢ+ (" σ₂ ", " ctx₂ ")" => InstExecution σ₁ ctx₁ σ₂ ctx₂

-- To model when the execution has finished at an instant, we define a property of a reactor being
-- stuck in that instant: when there is no instanteneous step it can take
abbrev instStuck (σ : Reactor ι υ) (ctx : Context ι) := ∀ σ' ctx', ¬ (σ, ctx) ⇓ᵢ (σ', ctx')

structure StuckInstExecution (σ₁ : Reactor ι υ) (ctx₁ : Context ι) (σ₂ : Reactor ι υ) (ctx₂ : Context ι) : Prop where
  exec : (σ₁, ctx₁) ⇓ᵢ+ (σ₂, ctx₂)
  stuck : instStuck σ₂ ctx₂

notation "(" σ₁ ", " ctx₁ ") ⇓ᵢ| (" σ₂ ", " ctx₂ ")" => StuckInstExecution σ₁ ctx₁ σ₂ ctx₂

-- Now we define a fully timed step, which can be a full instaneous execution, i.e. until no more
-- steps can be taken, or a time advancement.
inductive Step (σ : Reactor ι υ) (ctx : Context ι) : Reactor ι υ → Context ι → Prop 
  | instToStuck {σ' ctx'} : (σ, ctx) ⇓ᵢ| (σ', ctx') → Step σ ctx σ' ctx'
  | advanceTime {σ' g} (hg : ctx.time < g) :
    (g ∈ σ.scheduledTags) →
    (∀ g' ∈ σ.scheduledTags, ctx.time < g' → g ≤ g') →
    (ctx.currentExecutedRcns = σ.rcns.ids) →
    (σ.eqWithClearedPorts σ') →
    Step σ ctx σ' (ctx.advanceTime hg)

notation "(" σ₁ ", " ctx₁ ") ⇓ (" σ₂ ", " ctx₂ ")" => Step σ₁ ctx₁ σ₂ ctx₂

def sameReactionExecuted
{σ₁ σ₂ σ₁' σ₂' : Reactor ι υ}
{ctx₁ ctx₂ ctx₁' ctx₂'  : Context ι} 
(H1 : (σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁'))
(H2 : (σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) : Prop :=
  ∃ i : ι, (i ∉ ctx₁.currentExecutedRcns) ∧ (i ∉ ctx₂.currentExecutedRcns) ∧ 
  (i ∈ ctx₁'.currentExecutedRcns) ∧ (i ∈ ctx₂'.currentExecutedRcns)

def sameReactionTopologyChanges
{σ₁ σ₂ σ₁' σ₂' : Reactor ι υ}
{ctx₁ ctx₂ ctx₁' ctx₂'  : Context ι} 
(H1 : (σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁'))
(H2 : (σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) : Prop :=
  (∀ i : ι, (i ∈ σ₁.rcns.ids ∧ i ∉ σ₁'.rcns.ids) → (i ∈ σ₂.rcns.ids ∧ i ∉ σ₁'.rcns.ids)) ∧   -- reaction deleted  
  (∀ i : ι, ((i ∉ σ₁.rcns.ids) ∧ i ∈ σ₁'.rcns.ids) → ((i ∉ σ₂.rcns.ids) ∧ i ∈ σ₁'.rcns.ids)) -- reaction added  

end Execution

open Execution

-- An execution of a reactor model is a series of execution steps.
-- We model this with a reflexive transitive closure:
inductive Execution : Reactor ι υ → Context ι → Reactor ι υ → Context ι → Prop
  | refl (σ ctx) : Execution σ ctx σ ctx
  | step {σ₁ ctx₁ σ₂ ctx₂ σ₃ ctx₃} : (σ₁, ctx₁) ⇓ (σ₂, ctx₂) → Execution σ₂ ctx₂ σ₃ ctx₃ → Execution σ₁ ctx₁ σ₃ ctx₃

notation "(" σ₁ ", " ctx₁ ") ⇓* (" σ₂ ", " ctx₂ ")" => Execution σ₁ ctx₁ σ₂ ctx₂