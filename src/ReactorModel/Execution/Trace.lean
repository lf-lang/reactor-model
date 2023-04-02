import ReactorModel.Execution.State

open Classical

variable [ReactorType.Indexable α]

namespace Execution
namespace Instantaneous
namespace Step

variable {s₁ s₂ : State α}

inductive _root_.Execution.Instantaneous.Step : State α → State α → Type  
  | skip : (s.Allows rcn) → (¬s.Triggers rcn) → Step s (s.record rcn)
  | exec : (s.Allows rcn) → (s.Triggers rcn) → Step s (s.exec rcn |>.record rcn)

notation s₁:max " ⇓ᵢ " s₂:max => Step s₁ s₂

def rcn : (s₁ ⇓ᵢ s₂) → ID
  | skip (rcn := rcn) .. | exec (rcn := rcn) .. => rcn

def allows_rcn : (e : s₁ ⇓ᵢ s₂) → s₁.Allows e.rcn
  | skip h .. | exec h .. => h

end Step

-- TODO?: Once all else is settled, return this to being only transitive but not reflexive.
--        Then you can remove the `fresh` condiction on `ClosedExecution`.
inductive Execution : State α → State α → Type
  | refl : Execution s s
  | trans : (s₁ ⇓ᵢ s₂) → (Execution s₂ s₃) → Execution s₁ s₃

notation s₁:max " ⇓ᵢ* " s₂:max => Execution s₁ s₂

def Execution.rcns {s₁ s₂ : State α} : (s₁ ⇓ᵢ* s₂) → List ID
  | refl => []
  | trans hd tl => hd.rcn :: tl.rcns

structure ClosedExecution (s₁ s₂ : State α) where  
  exec   : s₁ ⇓ᵢ* s₂
  fresh  : s₁.progress = ∅ 
  closed : s₂.Closed
  
notation s₁:max " ⇓| " s₂:max => ClosedExecution s₁ s₂

abbrev ClosedExecution.rcns {s₁ s₂ : State α} (e : s₁ ⇓| s₂) : List ID :=
  e.exec.rcns

end Instantaneous

-- Note: We don't clear the ports here.
structure AdvanceTag (s₁ s₂ : State α) where
  closed : s₁.Closed 
  advance : s₁.Advance s₂

notation s₁:max " ⇓- " s₂:max => AdvanceTag s₁ s₂

inductive Step (s₁ s₂ : State α)
  | close (h : s₁ ⇓| s₂)
  | advance (h : s₁ ⇓- s₂)

notation s₁:max " ⇓ " s₂:max => Step s₁ s₂

end Execution

open Execution

inductive Execution : State α → State α → Type
  | refl : Execution s s
  | step : (s₁ ⇓ s₂) → (Execution s₂ s₃) → Execution s₁ s₃

notation s₁ " ⇓* " s₂ => Execution s₁ s₂