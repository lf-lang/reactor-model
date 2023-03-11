import ReactorModel.Execution.State
import ReactorModel.Execution.Schedule

open Classical

namespace Execution

inductive ChangeStep (s : State) : State → Identified Change → Prop 
  | port :   (s.rtr -[(.prt k):i   fun _ => v]→ σ') → ChangeStep s { s with rtr := σ' } ⟨rcn, .port k i v⟩
  | state :  (s.rtr -[.stv:i       fun _ => v]→ σ') → ChangeStep s { s with rtr := σ' } ⟨rcn, .state i v⟩
  | action : (s.rtr -[.act:i (schedule · t v)]→ σ') → ChangeStep s { s with rtr := σ' } ⟨rcn, .action i t v⟩
  -- Mutations are (temporarily) no-ops:
  | connect :    ChangeStep s s ⟨rcn, .mut $ .connect i₁ i₂⟩
  | disconnect : ChangeStep s s ⟨rcn, .mut $ .disconnect i₁ i₂⟩
  | create :     ChangeStep s s ⟨rcn, .mut $ .create rtr⟩
  | delete :     ChangeStep s s ⟨rcn, .mut $ .delete i⟩
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
  | skip : OperationStep s (s.record rcn) (.skip rcn)
  | exec : (s₁ -[cs.map (⟨rcn, ·⟩)]→* s₂) → OperationStep s₁ (s₂.record rcn) (.exec rcn cs)

notation s₁:max " -[" op "]↣ " s₂:max => OperationStep s₁ s₂ op

structure InstStep (s₁ s₂ : State) where
  op : Operation
  wfOp : s₁.operation op.rcn = op
  allows : s₁.Allows op.rcn
  exec : s₁ -[op]↣ s₂

notation s₁:max " ⇓ᵢ " s₂:max => InstStep s₁ s₂

def InstStep.rcn (e : s₁ ⇓ᵢ s₂) : ID := e.op.rcn

inductive InstExecution : State → State → Type
  | refl : InstExecution s s
  | trans : (s₁ ⇓ᵢ s₂) → (InstExecution s₂ s₃) → InstExecution s₁ s₃

notation s₁:max " ⇓ᵢ* " s₂:max => InstExecution s₁ s₂

def InstExecution.appendStep : (s₁ ⇓ᵢ* s₂) → (s₂ ⇓ᵢ s₃) → (s₁ ⇓ᵢ* s₃)
  | refl, e₂ => trans e₂ refl
  | trans e₁ e₂, e₃ => trans e₁ (e₂.appendStep e₃) 

instance : HAppend (s₁ ⇓ᵢ* s₂) (s₂ ⇓ᵢ s₃) (s₁ ⇓ᵢ* s₃) where
  hAppend e₁ e₂ := e₁.appendStep e₂

def InstExecution.append : (s₁ ⇓ᵢ* s₂) → (s₂ ⇓ᵢ* s₃) → (s₁ ⇓ᵢ* s₃)
  | refl, e₂ => e₂
  | trans e₁ e₂, e₃ => trans e₁ (e₂.append e₃) 

instance : HAppend (s₁ ⇓ᵢ* s₂) (s₂ ⇓ᵢ* s₃) (s₁ ⇓ᵢ* s₃) where
  hAppend e₁ e₂ := e₁.append e₂

/-def InstExecution.nthState : (e : s₁ ⇓ᵢ* s₂) → Nat → Option State
  | _,          0     => s₁
  | trans _ tl, n + 1 => tl.nthState n
  | single _,   _ + 1 => none-/

def InstExecution.ops : (s₁ ⇓ᵢ* s₂) → List Operation
  | refl => []
  | trans hd tl => hd.op :: tl.ops

def InstExecution.rcns (e : s₁ ⇓ᵢ* s₂) : List ID :=
  e.ops.map Operation.rcn

def InstExecution.changes (e : s₁ ⇓ᵢ* s₂) : List (Identified Change) :=
  e.ops.map (·.changes) |>.join

open State (Closed)

structure ClosedExecution (s₁ s₂ : State) : Type where  
  exec   : s₁ ⇓ᵢ* s₂
  fresh  : s₁.progress = ∅ 
  closed : Closed s₂
  
notation s₁:max " ⇓| " s₂:max => ClosedExecution s₁ s₂

abbrev ClosedExecution.rcns (e : s₁ ⇓| s₂) : List ID :=
  e.exec.rcns

-- Note: We don't clear the ports here. Thus, we define a more relaxed version of the reactor model
--       for which we can still prove determinism.
structure AdvanceTag (s₁ s₂ : State) where
  closed : Closed s₁ 
  advance : s₁.Advance s₂

notation s₁:max " ⇓- " s₂:max => AdvanceTag s₁ s₂

inductive Step (s₁ s₂ : State) : Type 
  | close (h : s₁ ⇓| s₂)
  | advance (h : s₁ ⇓- s₂)

notation s₁:max " ⇓ " s₂:max => Step s₁ s₂

end Execution

open Execution

inductive Execution : State → State → Type
  | refl : Execution s s
  | step : (s₁ ⇓ s₂) → (Execution s₂ s₃) → Execution s₁ s₃

notation s₁ " ⇓* " s₂ => Execution s₁ s₂