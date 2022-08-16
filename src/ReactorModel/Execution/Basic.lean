import ReactorModel.Execution.State

namespace Execution

-- NOTE: This does not constrain actions to have to be scheduled into the future.
--       If we schedule something for the past, it doesn't matter, since that action value will never be read.
--       But if the current tag has a microstep of 0, it is possible to schedule something for the current tag
--       (in the `none` case).
noncomputable def schedule (act : Time.Tag ⇉ Value) (t : Time) (v : Value) : Time.Tag ⇉ Value :=
  match act.ids.filter (·.time = t) |>.max with
  | none => act.update ⟨t, 0⟩ v
  | some g => act.update ⟨t, g.microstep + 1⟩ v

inductive ChangeStep (s : State) : State → Identified Change → Prop 
  | port :   (s.rtr -[.prt:i (⟨v, ·.kind⟩)]→ σ')    → ChangeStep s ⟨σ', s.ctx⟩ ⟨rcn, .port i v⟩
  | state :  (s.rtr -[.stv:i λ _ => v]→ σ')         → ChangeStep s ⟨σ', s.ctx⟩ ⟨rcn, .state i v⟩
  | action : (s.rtr -[.act:i (schedule · t v)]→ σ') → ChangeStep s ⟨σ', s.ctx⟩ ⟨rcn, .action i t v⟩
  -- Mutations are (temporarily) no-ops:
  | connect :    ChangeStep s s ⟨rcn, .connect i₁ i₂⟩
  | disconnect : ChangeStep s s ⟨rcn, .disconnect i₁ i₂⟩
  | create :     ChangeStep s s ⟨rcn, .create rtr⟩
  | delete :     ChangeStep s s ⟨rcn, .delete i⟩
  -- | connect {σ' src dst r} :    (s.rtr &[.rcn:rcn]= r) → (s.rtr -[Cmp.rcn|r (·.update (s.freshID Cmp.rcn r) (Reaction.relay src dst))]→ σ') → ChangeStep rcn s ⟨σ', s.ctx⟩ (.connect src dst)
  -- | disconnect {σ' src dst r} : (s.rtr &[.rcn:rcn]= r) → (s.rtr -[Cmp.rcn|r (·.filter' (· ≠ Reaction.relay src dst))]→ σ')                  → ChangeStep rcn s ⟨σ', s.ctx⟩ (.disconnect src dst)
  -- TODO: `create` via reactor class instantiation function
  -- | delete {σ' i r} :           (s.rtr &[.rcn:rcn]= r) → (s.rtr -[Cmp.rtr|r (·.update i none)]→ σ')                                         → ChangeStep rcn s ⟨σ', s.ctx⟩ (.delete i)

notation s₁:max " -[" c "]→ " s₂:max => ChangeStep s₁ s₂ c

inductive ChangeListStep : State → State → (List $ Identified Change) → Prop
  | nil : ChangeListStep s s []
  | cons : (s₁ -[hd]→ s₂) → (ChangeListStep s₂ s₃ tl) → ChangeListStep s₁ s₃ (hd::tl)

notation s₁:max " -[" cs "]→* " s₂:max => ChangeListStep s₁ s₂ cs

-- We separate the execution into two parts, the instantaneous execution which controlls
-- how reactors execute at a given instant, and the timed execution, which includes the
-- passing of time
inductive InstStep (s : State) : State → Type 
  | execReaction : 
    (s.allows rcn) →
    (s.triggers rcn) →
    (s.rcnOutput' rcn = some o) →
    (s -[o]→* s') →
    InstStep s ⟨s'.rtr, s'.ctx.addCurrentProcessed rcn⟩
  | skipReaction :
    (s.rtr.contains .rcn rcn) →
    (s.allows rcn) →
    (¬ s.triggers rcn) →
    InstStep s ⟨s.rtr, s.ctx.addCurrentProcessed rcn⟩

notation s₁:max " ⇓ᵢ " s₂:max => InstStep s₁ s₂

def InstStep.rcn : (s₁ ⇓ᵢ s₂) → ID
  | execReaction (rcn := rcn) .. => rcn
  | skipReaction (rcn := rcn) .. => rcn

inductive InstStep.ChangeBlock
  | skip (rcn : ID)
  | exec (rcn : ID) (cs : List (Identified Change))

def InstStep.ChangeBlock.rcn : InstStep.ChangeBlock → ID 
  | skip rcn | exec rcn _ => rcn

instance : Coe InstStep.ChangeBlock (List $ Identified Change) where
  coe 
    | .skip _ => []
    | .exec _ cs => cs

def InstStep.changes : (s₁ ⇓ᵢ s₂) → ChangeBlock
  | execReaction (rcn := rcn) (o := cs) .. => .exec rcn cs
  | skipReaction (rcn := rcn) .. => .skip rcn

-- An execution at an instant is a series of steps,
-- which we model with the transitive closure.
inductive InstExecution : State → State → Type
  | single : (s₁ ⇓ᵢ s₂) → InstExecution s₁ s₂
  | trans : (s₁ ⇓ᵢ s₂) → (InstExecution s₂ s₃) → InstExecution s₁ s₃

notation s₁:max " ⇓ᵢ+ " s₂:max => InstExecution s₁ s₂

def InstExecution.appendStep : (s₁ ⇓ᵢ+ s₂) → (s₂ ⇓ᵢ s₃) → (s₁ ⇓ᵢ+ s₃)
  | single e₁, e₂ => trans e₁ (single e₂)
  | trans e₁ e₂, e₃ => trans e₁ (e₂.appendStep e₃) 

instance : HAppend (s₁ ⇓ᵢ+ s₂) (s₂ ⇓ᵢ s₃) (s₁ ⇓ᵢ+ s₃) where
  hAppend e₁ e₂ := e₁.appendStep e₂

def InstExecution.append : (s₁ ⇓ᵢ+ s₂) → (s₂ ⇓ᵢ+ s₃) → (s₁ ⇓ᵢ+ s₃)
  | single e₁, e₂ => trans e₁ e₂
  | trans e₁ e₂, e₃ => trans e₁ (e₂.append e₃) 

instance : HAppend (s₁ ⇓ᵢ+ s₂) (s₂ ⇓ᵢ+ s₃) (s₁ ⇓ᵢ+ s₃) where
  hAppend e₁ e₂ := e₁.append e₂

def InstExecution.rcns : (s₁ ⇓ᵢ+ s₂) → List ID
  | single e => [e.rcn]
  | trans hd tl => hd.rcn :: tl.rcns

/-def InstExecution.nthState : (e : s₁ ⇓ᵢ+ s₂) → Nat → Option State
  | _,          0     => s₁
  | trans _ tl, n + 1 => tl.nthState n
  | single _,   _ + 1 => none-/

def InstExecution.changes : (s₁ ⇓ᵢ+ s₂) → List InstStep.ChangeBlock
  | single e => [e.changes]
  | trans hd tl => hd.changes :: tl.changes

def InstExecution.changes' (e : s₁ ⇓ᵢ+ s₂) : List (Identified Change) :=
  e.changes.map (λ cs => ↑cs) |>.join

abbrev State.instComplete (s : State) : Prop := s.ctx.currentProcessedRcns = s.rtr.ids .rcn

structure CompleteInstExecution (s₁ s₂ : State) where
  exec : s₁ ⇓ᵢ+ s₂ 
  complete : s₂.instComplete
  
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