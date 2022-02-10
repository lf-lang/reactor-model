import ReactorModel.Execution.State

open Port

variable {ι υ} [Value υ]

-- TODO: Come up with something nicer.
structure Reactor.eqWithClearedPorts (σ₁ σ₂ : Reactor ι υ) where
  otherCmpsEq : ∀ {cmp}, cmp ≠ Cmp.prt → cmp.accessor σ₁ = cmp.accessor σ₂
  samePortIDs : ∀ i, σ₁.containsID i Cmp.prt ↔ σ₂.containsID i Cmp.prt
  clearedPorts : ∀ i p, σ₁ *[Cmp.prt, i]= p → σ₂ *[Cmp.prt, i]= { p .. with val := ⊥ }

lemma Reactor.eqWithClearedPortsUnique {σ σ₁ σ₂ : Reactor ι υ} :
 Reactor.eqWithClearedPorts σ σ₁ → Reactor.eqWithClearedPorts σ σ₂ → 
 σ₁ = σ₂ := sorry
 
namespace Execution

inductive ChangeStep (g : Time.Tag) (σ₁ : Reactor ι υ) : Reactor ι υ → Change ι υ → Prop 
  | port (σ₂) {i v} : (σ₁ -[Cmp.Field.prtVal, i := v]→ σ₂) → ChangeStep g σ₁ σ₂ (Change.port i v) -- Port propagation isn't necessary/possible, because we're using relay reactions. 
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
inductive InstStep (s : State ι υ) : State ι υ → Prop 
  | execReaction {rcn : Reaction ι υ} {i σ'} : 
    (s.rtr.rcns i = rcn) →
    (s.rtr.predecessors rcn ⊆ s.ctx.currentExecutedRcns) →
    (i ∉ s.ctx.currentExecutedRcns) →
    (rcn.triggersOn $ σ.inputForRcn rcn s.ctx.time) →
    (σ -[rcn $ σ.inputForRcn rcn s.ctx.time, s.ctx.time]→* σ') →
    InstStep s ⟨σ', s.ctx.addCurrentExecuted i⟩
  | skipReaction {rcn : Reaction ι υ} {i} :
    (s.rtr.rcns i = rcn) →
    (s.rtr.predecessors rcn ⊆ s.ctx.currentExecutedRcns) →
    (i ∉ s.ctx.currentExecutedRcns) →
    (¬(rcn.triggersOn $ s.rtr.inputForRcn rcn s.ctx.time)) →
    InstStep s ⟨σ, s.ctx.addCurrentExecuted i⟩

notation s₁:max " ⇓ᵢ " s₂:max => InstStep s₁ s₂

-- An execution at an instant is a series of steps,
-- which we model with the transitive closure.
inductive InstExecution : State ι υ → State ι υ → Prop 
  | single {s₁ s₂} : s₁ ⇓ᵢ s₂ → InstExecution s₁ s₂
  | trans {s₁ s₂ s₃} : s₁ ⇓ᵢ s₂ → InstExecution s₂ s₃ → InstExecution s₁ s₃

notation s₁:max " ⇓ᵢ+ " s₂:max => InstExecution s₁ s₂

abbrev State.instComplete (s : State ι υ) := s.ctx.currentExecutedRcns = s.rtr.rcns.ids

structure CompleteInstExecution (s₁ s₂ : State ι υ) : Prop where
  exec : s₁ ⇓ᵢ+ s₂
  complete : s₂.instComplete

notation s₁:max " ⇓ᵢ| " s₂:max => CompleteInstExecution s₁ s₂

-- Now we define a fully timed step, which can be a full instaneous execution, i.e. until no more
-- steps can be taken, or a time advancement.
inductive Step (s : State ι υ) : State ι υ → Prop 
  | completeInst (s') : s ⇓ᵢ| s' → Step s s'
  | advanceTime {σ' g} (hg : s.isNextTag g) :
    (s.ctx.currentExecutedRcns = s.rtr.rcns.ids) →
    (s.rtr.eqWithClearedPorts σ') →
    Step s ⟨σ', s.ctx.advanceTime g hg.lower⟩

notation s₁:max " ⇓ " s₂:max => Step s₁ s₂

/-
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
-/

end Execution

open Execution

-- An execution of a reactor model is a series of execution steps.
-- We model this with a reflexive transitive closure:
inductive Execution : State ι υ → State ι υ → Prop
  | refl (s) : Execution s s
  | step (s₁) {s₂} (s₃) : s₁ ⇓ s₂ → Execution s₂ s₃ → Execution s₁ s₃

notation s₁ " ⇓* " s₂ => Execution s₁ s₂