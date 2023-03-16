import ReactorModel.Execution.State

open Classical

namespace Execution

inductive InstStep : State → State → Type  
  | skip : (s.Allows rcn.id) → (¬s.Triggers rcn) → InstStep s (s.record rcn.id)
  | exec : (s.Allows rcn.id) → (s.Triggers rcn)  → InstStep s (s.exec rcn |>.record rcn.id)

notation s₁:max " ⇓ᵢ " s₂:max => InstStep s₁ s₂

def InstStep.rcn : (s₁ ⇓ᵢ s₂) → s₁.rtr.Valid .rcn
  | skip (rcn := rcn) .. | exec (rcn := rcn) .. => rcn

def InstStep.allows_rcn : (e : s₁ ⇓ᵢ s₂) → s₁.Allows e.rcn
  | skip h _ | exec h _ => h

-- TODO?: Once all else is settled, return this to being only transitive but not reflexive.
--        Then you can remove the `fresh` condiction on `ClosedExecution`.
inductive InstExecution : State → State → Type
  | refl : InstExecution s s
  | trans : (s₁ ⇓ᵢ s₂) → (InstExecution s₂ s₃) → InstExecution s₁ s₃

notation s₁:max " ⇓ᵢ* " s₂:max => InstExecution s₁ s₂

def InstExecution.rcns : (s₁ ⇓ᵢ* s₂) → List ID
  | refl => []
  | trans hd tl => hd.rcn :: tl.rcns

open State (Closed)

structure ClosedExecution (s₁ s₂ : State) where  
  exec   : s₁ ⇓ᵢ* s₂
  fresh  : s₁.progress = ∅ 
  closed : Closed s₂
  
notation s₁:max " ⇓| " s₂:max => ClosedExecution s₁ s₂

abbrev ClosedExecution.rcns (e : s₁ ⇓| s₂) : List ID :=
  e.exec.rcns

-- Note: We don't clear the ports here.
structure AdvanceTag (s₁ s₂ : State) where
  closed : Closed s₁ 
  advance : s₁.Advance s₂

notation s₁:max " ⇓- " s₂:max => AdvanceTag s₁ s₂

inductive Step (s₁ s₂ : State)
  | close (h : s₁ ⇓| s₂)
  | advance (h : s₁ ⇓- s₂)

notation s₁:max " ⇓ " s₂:max => Step s₁ s₂

end Execution

open Execution

inductive Execution : State → State → Type
  | refl : Execution s s
  | step : (s₁ ⇓ s₂) → (Execution s₂ s₃) → Execution s₁ s₃

notation s₁ " ⇓* " s₂ => Execution s₁ s₂