import ReactorModel.Execution.State

open Port

-- TODO: Come up with something nicer.
structure Reactor.eqWithClearedPorts (σ₁ σ₂ : Reactor) where
  otherCmpsEq : ∀ {cmp}, cmp ≠ Cmp.prt → cmp.accessor σ₁ = cmp.accessor σ₂
  samePortIDs : σ₁.ids Cmp.prt = σ₂.ids Cmp.prt
  clearedPorts : ∀ i p, σ₁ *[Cmp.prt, i]= p → σ₂ *[Cmp.prt, i]= { p .. with val := ⊥ }

lemma Reactor.eqWithClearedPortsUnique {σ σ₁ σ₂ : Reactor} :
  Reactor.eqWithClearedPorts σ σ₁ → Reactor.eqWithClearedPorts σ σ₂ → 
  σ₁ = σ₂ := sorry

namespace Execution

noncomputable def schedule (acts : Time.Tag ▸ Value) (t : Time) (v : Value) : Time.Tag ▸ Value :=
  match acts.ids.filter (·.t = t) |>.max with
  | none => acts.update ⟨t, 0⟩ v
  | some g => acts.update ⟨t, g.microsteps + 1⟩ v

inductive ChangeStep (σ : Reactor) : Reactor → Change → Prop 
  | port {σ' i v} :     (σ -[Cmp.prt:i ({ · .. with val := v})]→ σ') → ChangeStep σ σ' (Change.port i v)
  | state {σ' i v} :    (σ -[Cmp.stv:i              (λ _ => v)]→ σ') → ChangeStep σ σ' (Change.state i v)
  | action {σ' i t v} : (σ -[Cmp.act:i        (schedule · t v)]→ σ') → ChangeStep σ σ' (Change.action i t v)
  -- Mutations are (temporarily) no-ops:
  | connect {i₁ i₂} :    ChangeStep σ σ (Change.connect i₁ i₂)
  | disconnect {i₁ i₂} : ChangeStep σ σ (Change.disconnect i₁ i₂)
  | create {rtr i} :     ChangeStep σ σ (Change.create rtr i)
  | delete {i} :         ChangeStep σ σ (Change.delete i)

notation σ₁:max " -[" c "]→ " σ₂:max => ChangeStep σ₁ σ₂ c

inductive ChangeListStep : Reactor → Reactor → List (Change) → Prop
  | nil (σ₁) : ChangeListStep σ₁ σ₁ []
  | cons {σ₁ σ₂ σ₃ hd tl} : (σ₁ -[hd]→ σ₂) → (ChangeListStep σ₂ σ₃ tl) → ChangeListStep σ₁ σ₃ (hd::tl)

notation σ₁:max " -[" cs "]→* " σ₂:max => ChangeListStep σ₁ σ₂ cs

-- We separate the execution into two parts, the instantaneous execution which controlls
-- how reactors execute at a given instant, and the timed execution, which includes the
-- passing of time
inductive InstStep (s : State) : State → Prop 
  | execReaction {rcn : Reaction} {i : ID} {σ} : 
    (s.rtr *[Cmp.rcn, i]= rcn) →
    (s.couldExec i) →
    (s.triggers rcn) →
    (s.rtr -[rcn $ s.rcnInput rcn]→* σ) →
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

-- Now we define a fully timed step, which can be a full instaneous execution, i.e. until no more
-- steps can be taken, or a time advancement.
inductive Step (s : State) : State → Prop 
  | completeInst (s') : s ⇓ᵢ| s' → Step s s'
  | advanceTime {σ} {g : Time.Tag} (hg : s.nextTag = g) :
    (s.instComplete) →
    (s.rtr.eqWithClearedPorts σ) →
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