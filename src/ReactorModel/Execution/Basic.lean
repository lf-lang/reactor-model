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

inductive OperationStep : State → State → Operation → Prop
  | skip : OperationStep s ⟨s.rtr, s.ctx.addCurrentProcessed rcn⟩ (.skip rcn)
  | exec : (s₁ -[cs.map (⟨rcn, ·⟩)]→* s₂) → OperationStep s₁ ⟨s₂.rtr, s₂.ctx.addCurrentProcessed rcn⟩ (.exec rcn cs)

notation s₁:max " -[" op "]↣ " s₂:max => OperationStep s₁ s₂ op

structure InstStep (s₁ s₂ : State) where
  op : Operation
  wfOp : s₁.operation op.rcn = op
  allows : s₁.allows op.rcn
  exec : s₁ -[op]↣ s₂

notation s₁:max " ⇓ᵢ " s₂:max => InstStep s₁ s₂

def InstStep.rcn (e : s₁ ⇓ᵢ s₂) : ID := e.op.rcn

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

/-def InstExecution.nthState : (e : s₁ ⇓ᵢ+ s₂) → Nat → Option State
  | _,          0     => s₁
  | trans _ tl, n + 1 => tl.nthState n
  | single _,   _ + 1 => none-/

def InstExecution.ops : (s₁ ⇓ᵢ+ s₂) → List Operation
  | single e => [e.op]
  | trans hd tl => hd.op :: tl.ops

def InstExecution.rcns (e : s₁ ⇓ᵢ+ s₂) : List ID :=
  e.ops.map (·.rcn)

def InstExecution.changes (e : s₁ ⇓ᵢ+ s₂) : List (Identified Change) :=
  e.ops.map (·.changes) |>.join

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