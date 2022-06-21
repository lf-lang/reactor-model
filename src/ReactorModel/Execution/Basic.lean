import ReactorModel.Execution.State

open Port

namespace Execution

noncomputable def schedule (act : Time.Tag ⇉ Value) (t : Time) (v : Value) : Time.Tag ⇉ Value :=
  match act.ids.filter (·.time = t) |>.max with
  | none => act.update ⟨t, 0⟩ v
  | some g => act.update ⟨t, g.microsteps + 1⟩ v

inductive ChangeStep (rcn : ID) (s : State) : State → Change → Prop 
  | port :   (s.rtr -[.prt:i (⟨v, ·.kind⟩)]→ σ')    → ChangeStep rcn s ⟨σ', s.ctx⟩ (.port i v)
  | state :  (s.rtr -[.stv:i λ _ => v]→ σ')         → ChangeStep rcn s ⟨σ', s.ctx⟩ (.state i v)
  | action : (s.rtr -[.act:i (schedule · t v)]→ σ') → ChangeStep rcn s ⟨σ', s.ctx⟩ (.action i t v)
  -- Mutations are (temporarily) no-ops:
  | connect :    ChangeStep rcn s s (.connect i₁ i₂)
  | disconnect : ChangeStep rcn s s (.disconnect i₁ i₂)
  | create :     ChangeStep rcn s s (.create rtr)
  | delete :     ChangeStep rcn s s (.delete i)
  -- | connect {σ' src dst r} :    (s.rtr &[.rcn:rcn]= r) → (s.rtr -[Cmp.rcn|r (·.update (s.freshID Cmp.rcn r) (Reaction.relay src dst))]→ σ') → ChangeStep rcn s ⟨σ', s.ctx⟩ (.connect src dst)
  -- | disconnect {σ' src dst r} : (s.rtr &[.rcn:rcn]= r) → (s.rtr -[Cmp.rcn|r (·.filter' (· ≠ Reaction.relay src dst))]→ σ')                  → ChangeStep rcn s ⟨σ', s.ctx⟩ (.disconnect src dst)
  -- TODO: `create` via reactor class instantiation function
  -- | delete {σ' i r} :           (s.rtr &[.rcn:rcn]= r) → (s.rtr -[Cmp.rtr|r (·.update i none)]→ σ')                                         → ChangeStep rcn s ⟨σ', s.ctx⟩ (.delete i)

notation s₁:max " -[" rcn ":" c "]→ " s₂:max => ChangeStep rcn s₁ s₂ c

inductive ChangeListStep (rcn : ID) : State → State → (List Change) → Prop
  | nil : ChangeListStep rcn s s []
  | cons : (s₁ -[rcn:hd]→ s₂) → (ChangeListStep rcn s₂ s₃ tl) → ChangeListStep rcn s₁ s₃ (hd::tl)

notation s₁:max " -[" rcn ":" cs "]→* " s₂:max => ChangeListStep rcn s₁ s₂ cs

/-
inductive ChangeListStep : State → State → List (Identified Change) → Prop
  | nil (s) : ChangeListStep s s []
  | cons {s₁ s₂ s₃ rcn hd tl} : (s₁ -[rcn:hd]→ s₂) → (ChangeListStep s₂ s₃ tl) → ChangeListStep s₁ s₃ (⟨rcn, hd⟩::tl)

notation s₁:max " -[" rcs "]→* " s₂:max => ChangeListStep s₁ s₂ rcs

abbrev ChangeListStep.uniform (s₁ s₂ : State) (rcn : ID) (cs : List Change) : Prop :=
  s₁ -[cs.map (⟨rcn, ·⟩)]→* s₂

notation s₁:max " -[" rcn ":" cs "]→* " s₂:max => ChangeListStep.uniform s₁ s₂ rcn cs
-/

-- We separate the execution into two parts, the instantaneous execution which controlls
-- how reactors execute at a given instant, and the timed execution, which includes the
-- passing of time
inductive InstStep (s : State) (rcn : ID) : State → Prop 
  | execReaction : 
    (s.allows rcn) →
    (s.triggers rcn) →
    (s.rcnOutput rcn = some o) →
    (s -[rcn:o]→* s') →
    InstStep s rcn ⟨s'.rtr, s'.ctx.addCurrentProcessed rcn⟩
  | skipReaction :
    (s.rtr.contains .rcn rcn) →
    (s.allows rcn) →
    (¬ s.triggers rcn) →
    InstStep s rcn ⟨s.rtr, s.ctx.addCurrentProcessed rcn⟩

notation s₁:max " ⇓ᵢ[" rcn "] " s₂:max => InstStep s₁ rcn s₂

-- An execution at an instant is a series of steps,
-- which we model with the transitive closure.
inductive InstExecution : State → List ID → State → Prop 
  | single : (s₁ ⇓ᵢ[rcn] s₂) → InstExecution s₁ [rcn] s₂
  | trans : (s₁ ⇓ᵢ[hd] s₂) → (InstExecution s₂ tl s₃) → InstExecution s₁ (hd::tl) s₃

notation s₁:max " ⇓ᵢ+[" rcns "] " s₂:max => InstExecution s₁ rcns s₂

abbrev State.instComplete (s : State) : Prop := s.ctx.currentProcessedRcns = s.rtr.ids .rcn

inductive CompleteInstExecution (s₁ s₂ : State) : Prop
  | mk : (rcns : List ID) → (s₁ ⇓ᵢ+[rcns] s₂) → s₂.instComplete → CompleteInstExecution s₁ s₂
  
notation s₁:max " ⇓ᵢ| " s₂:max => CompleteInstExecution s₁ s₂

def clearingPorts (σ₁ σ₂ : Reactor) : Prop := sorry -- TODO: Define this via MultiUpdate if that is realized.
theorem clearingPorts_unique : clearingPorts σ σ₁ → clearingPorts σ σ₂ → σ₁ = σ₂ := sorry

-- Now we define a fully timed step, which can be a full instaneous execution, i.e. until no more
-- steps can be taken, or a time advancement.
inductive Step (s : State) : State → Prop 
  | completeInst : (s ⇓ᵢ| s') → Step s s'
  | advanceTag :
    (hg : s.nextTag = some g) →
    (s.instComplete) →
    (clearingPorts s.rtr σ) →
    Step s ⟨σ, s.ctx.advanceTag g $ s.tag_lt_nextTag hg⟩

notation s₁:max " ⇓ " s₂:max => Step s₁ s₂

end Execution

open Execution

-- An execution of a reactor model is a series of execution steps.
-- We model this with a reflexive transitive closure:
inductive Execution : State → State → Prop
  | refl : Execution s s
  | step : (s₁ ⇓ s₂) → (Execution s₂ s₃) → Execution s₁ s₃

notation s₁ " ⇓* " s₂ => Execution s₁ s₂