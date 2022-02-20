import ReactorModel.Execution.State

open Port

namespace Execution

noncomputable def schedule (act : Time.Tag ▸ Value) (t : Time) (v : Value) : Time.Tag ▸ Value :=
  match act.ids.filter (·.t = t) |>.max with
  | none => act.update ⟨t, 0⟩ v
  | some g => act.update ⟨t, g.microsteps + 1⟩ v

-- PROBLEM: This new ID is not unique -> this will cause trouble wrt determinism.
-- Easy fix: Add the id of the new reaction as part of Change.connect and require 
--           that that id must be new (by a reactor constraint).
--           Then it's a simple Finmap.update.
def insertingRelayReaction (src dst : ID) (rcns₁ rcns₂ : ID ▸ Reaction) : Prop :=
  ∃ i, (i ∉ rcns₁.ids) ∧ (rcns₂ i = Reaction.relay src dst) ∧ ∀ j, j ≠ i → rcns₁ j = rcns₂ j

inductive ChangeStep (rcn : ID) (σ : Reactor) : Reactor → Change → Prop 
  | port {σ' i v} :     (σ -[Cmp.prt:i (⟨·.role, v⟩)]→ σ')    → ChangeStep rcn σ σ' (Change.port i v)
  | state {σ' i v} :    (σ -[Cmp.stv:i λ _ => v]→ σ')         → ChangeStep rcn σ σ' (Change.state i v)
  | action {σ' i t v} : (σ -[Cmp.act:i (schedule · t v)]→ σ') → ChangeStep rcn σ σ' (Change.action i t v)
  -- | connect {σ' src dst r} :    (σ &[rcn]= r) → (σ -[Cmp.rcn/r insertingRelayReaction src dst]→ σ')           → ChangeStep rcn σ σ' (Change.connect src dst)
  -- | disconnect {σ' src dst r} : (σ &[rcn]= r) → (σ -[Cmp.rcn|r (·.filter' (· ≠ Reaction.relay src dst))]→ σ') → ChangeStep rcn σ σ' (Change.disconnect src dst)
  -- | create {σ' rtr i r} :       (σ &[rcn]= r) → (σ -[Cmp.rtr|r (·.update i (some rtr))]→ σ')                  → ChangeStep rcn σ σ' (Change.create rtr i)
  -- | delete {σ' i r} :           (σ &[rcn]= r) → (σ -[Cmp.rtr|r (·.update i none)]→ σ')                        → ChangeStep rcn σ σ' (Change.create rtr i)
  -- Mutations are (temporarily) no-ops:
  | connect {i₁ i₂} :    ChangeStep rcn σ σ (Change.connect i₁ i₂)
  | disconnect {i₁ i₂} : ChangeStep rcn σ σ (Change.disconnect i₁ i₂)
  | create {rtr i} :     ChangeStep rcn σ σ (Change.create rtr i)
  | delete {i} :         ChangeStep rcn σ σ (Change.delete i)

notation σ₁:max " -[" rcn ":" c "]→ " σ₂:max => ChangeStep rcn σ₁ σ₂ c

inductive ChangeListStep (rcn : ID) : Reactor → Reactor → List (Change) → Prop
  | nil (σ₁) : ChangeListStep rcn σ₁ σ₁ []
  | cons {σ₁ σ₂ σ₃ hd tl} : (σ₁ -[rcn:hd]→ σ₂) → (ChangeListStep rcn σ₂ σ₃ tl) → ChangeListStep rcn σ₁ σ₃ (hd::tl)

notation σ₁:max " -[" rcn ":" cs "]→* " σ₂:max => ChangeListStep rcn σ₁ σ₂ cs

-- We separate the execution into two parts, the instantaneous execution which controlls
-- how reactors execute at a given instant, and the timed execution, which includes the
-- passing of time
inductive InstStep (s : State) : State → Prop 
  | execReaction {rcn : Reaction} {i : ID} {σ} : 
    (s.rtr *[Cmp.rcn, i]= rcn) →
    (s.couldExec i) →
    (s.triggers rcn) →
    (s.rtr -[i:rcn (s.rcnInput rcn)]→* σ) →
    InstStep s ⟨σ, s.ctx.addCurrentExecuted i⟩
  | skipReaction {rcn : Reaction} {i : ID} :
    (s.rtr *[Cmp.rcn, i]= rcn) →
    (s.couldExec i) →
    (¬ s.triggers rcn) →
    InstStep s ⟨s.rtr, s.ctx.addCurrentExecuted i⟩

notation s₁:max " ⇓ᵢ " s₂:max => InstStep s₁ s₂

-- An execution at an instant is a series of steps,
-- which we model with the transitive closure.
inductive InstExecution : State → State → Prop 
  | single {s₁ s₂} : s₁ ⇓ᵢ s₂ → InstExecution s₁ s₂
  | trans {s₁ s₂ s₃} : s₁ ⇓ᵢ s₂ → InstExecution s₂ s₃ → InstExecution s₁ s₃

notation s₁:max " ⇓ᵢ+ " s₂:max => InstExecution s₁ s₂

abbrev State.instComplete (s : State) : Prop := s.ctx.currentExecutedRcns = s.rtr.ids Cmp.rcn

structure CompleteInstExecution (s₁ s₂ : State) : Prop where
  exec : s₁ ⇓ᵢ+ s₂
  complete : s₂.instComplete

notation s₁:max " ⇓ᵢ| " s₂:max => CompleteInstExecution s₁ s₂

def clearingPorts (σ₁ σ₂ : Reactor) : Prop := sorry -- TODO: Define this via MultiUpdate if that is realized.
theorem clearingPorts_unique {σ σ₁ σ₂ : Reactor} : clearingPorts σ σ₁ → clearingPorts σ σ₂ → σ₁ = σ₂ :=  sorry

-- Now we define a fully timed step, which can be a full instaneous execution, i.e. until no more
-- steps can be taken, or a time advancement.
inductive Step (s : State) : State → Prop 
  | completeInst (s') : s ⇓ᵢ| s' → Step s s'
  | advanceTime {σ} {g : Time.Tag} (hg : s.nextTag = g) :
    (s.instComplete) →
    (clearingPorts s.rtr σ) →
    Step s ⟨σ, s.ctx.advanceTime g $ s.time_lt_nextTag hg⟩

notation s₁:max " ⇓ " s₂:max => Step s₁ s₂

end Execution

open Execution

-- An execution of a reactor model is a series of execution steps.
-- We model this with a reflexive transitive closure:
inductive Execution : State → State → Prop
  | refl (s) : Execution s s
  | step (s₁) {s₂} (s₃) : s₁ ⇓ s₂ → Execution s₂ s₃ → Execution s₁ s₃

notation s₁ " ⇓* " s₂ => Execution s₁ s₂