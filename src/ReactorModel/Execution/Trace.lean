import ReactorModel.Execution.State

open Classical

variable [ReactorType.Indexable α]

namespace Execution
namespace Instantaneous
namespace Step

variable {s₁ s₂ : State α}

inductive Skip : State α → State α → Type  
  | mk : (s.Allows rcn) → (¬s.Triggers rcn) → Skip s (s.record rcn)

notation s₁:max " ⇓ₛ " s₂:max => Skip s₁ s₂

def Skip.rcn : (s₁ ⇓ₛ s₂) → ID
  | mk (rcn := rcn) .. => rcn

def Skip.allows_rcn : (e : s₁ ⇓ₛ s₂) → s₁.Allows e.rcn
  | mk h .. => h

def Skip.not_triggers : (e : s₁ ⇓ₛ s₂) → ¬s₁.Triggers e.rcn
  | mk _ h => h

inductive Exec : State α → State α → Type  
  | mk : (s.Allows rcn) → (s.Triggers rcn) → Exec s (s.exec rcn |>.record rcn)

notation s₁:max " ⇓ₑ " s₂:max => Exec s₁ s₂

def Exec.rcn : (s₁ ⇓ₑ s₂) → ID
  | mk (rcn := rcn) .. => rcn

def Exec.allows_rcn : (e : s₁ ⇓ₑ s₂) → s₁.Allows e.rcn
  | mk h .. => h

inductive _root_.Execution.Instantaneous.Step (s₁ s₂ : State α)
  | skip (e : Skip s₁ s₂)
  | exec (e : Exec s₁ s₂)

notation s₁:max " ⇓ᵢ " s₂:max => Step s₁ s₂

def rcn : (s₁ ⇓ᵢ s₂) → ID
  | skip e | exec e => e.rcn

def allows_rcn : (e : s₁ ⇓ᵢ s₂) → s₁.Allows e.rcn
  | skip e | exec e => e.allows_rcn

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