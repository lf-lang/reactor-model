import ReactorModel.Execution.State

open Port

namespace Execution

noncomputable def schedule (act : Time.Tag ▸ Value) (t : Time) (v : Value) : Time.Tag ▸ Value :=
  match act.ids.filter (·.t = t) |>.max with
  | none => act.update ⟨t, 0⟩ v
  | some g => act.update ⟨t, g.microsteps + 1⟩ v

inductive ChangeStep (rcn : ID) (s : State) : State → Change → Prop 
  | port {σ' i v} :     (s.rtr -[Cmp.prt:i (⟨·.role, v⟩)]→ σ')    → ChangeStep rcn s ⟨σ', s.ctx⟩ (Change.port i v)
  | state {σ' i v} :    (s.rtr -[Cmp.stv:i λ _ => v]→ σ')         → ChangeStep rcn s ⟨σ', s.ctx⟩ (Change.state i v)
  | action {σ' i t v} : (s.rtr -[Cmp.act:i (schedule · t v)]→ σ') → ChangeStep rcn s ⟨σ', s.ctx⟩ (Change.action i t v)
  -- | connect {σ' src dst r} :    (s.rtr &[Cmp.rcn:rcn]= r) → (s.rtr -[Cmp.rcn|r (·.update s.freshID (Reaction.relay src dst))]→ σ') → ChangeStep rcn s ⟨σ', s.ctx⟩ (Change.connect src dst)
  -- | disconnect {σ' src dst r} : (s.rtr &[Cmp.rcn:rcn]= r) → (s.rtr -[Cmp.rcn|r (·.filter' (· ≠ Reaction.relay src dst))]→ σ')      → ChangeStep rcn s ⟨σ', s.ctx⟩ (Change.disconnect src dst)
  -- | create {σ' rtr r} :         (s.rtr &[Cmp.rcn:rcn]= r) → (s.rtr -[Cmp.rtr|r (·.update s.freshID (some rtr))]→ σ')               → ChangeStep rcn s ⟨σ', s.ctx⟩ (Change.create rtr)
  -- | delete {σ' i r} :           (s.rtr &[Cmp.rcn:rcn]= r) → (s.rtr -[Cmp.rtr|r (·.update i none)]→ σ')                             → ChangeStep rcn s ⟨σ', s.ctx⟩ (Change.delete i)
  -- Mutations are (temporarily) no-ops:
  | connect {i₁ i₂} :    ChangeStep rcn s s (Change.connect i₁ i₂)
  | disconnect {i₁ i₂} : ChangeStep rcn s s (Change.disconnect i₁ i₂)
  | create {rtr} :       ChangeStep rcn s s (Change.create rtr)
  | delete {i} :         ChangeStep rcn s s (Change.delete i)

notation s₁:max " -[" rcn ":" c "]→ " s₂:max => ChangeStep rcn s₁ s₂ c

inductive ChangeListStep (rcn : ID) : State → State → List Change → Prop
  | nil (s) : ChangeListStep rcn s s []
  | cons {s₁ s₂ s₃ hd tl} : (s₁ -[rcn:hd]→ s₂) → (ChangeListStep rcn s₂ s₃ tl) → ChangeListStep rcn s₁ s₃ (hd::tl)

notation s₁:max " -[" rcn ":" cs "]→* " s₂:max => ChangeListStep rcn s₁ s₂ cs

-- We separate the execution into two parts, the instantaneous execution which controlls
-- how reactors execute at a given instant, and the timed execution, which includes the
-- passing of time
inductive InstStep (s : State) : State → Prop 
  | execReaction {rcn : Reaction} {i : ID} {s' : State} : 
    (s.rtr *[Cmp.rcn:i]= rcn) →
    (s.couldExec i) →
    (s.triggers rcn) →
    (s -[i:rcn (s.rcnInput rcn)]→* s') →
    InstStep s ⟨s'.rtr, s'.ctx.addCurrentExecuted i⟩
  | skipReaction {rcn : Reaction} {i : ID} :
    (s.rtr *[Cmp.rcn:i]= rcn) →
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