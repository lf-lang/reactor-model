import ReactorModel.Execution.State

open Classical ReactorType Practical

variable [Practical α]

namespace Execution
namespace Instantaneous

-- TODO: Change this definition to use relations for the smaller steps.
--       We only need the constructive aspect of the functions in the proof of determinism.
--       That is, we don't need a reactor to be Updatable in order to define the execution model.
--       We *do* need it to be Updatable in the proof of determinism.
--       Once you've done this, move the requirement of Updatable from Proper to Practical.
inductive Step : State α → State α → Type  
  | skip : (s.Allows rcn) → (¬s.Triggers rcn) → Step s (s.record rcn)
  | exec : (s.Allows rcn) → (s.Triggers rcn) → Step s (s.exec rcn |>.record rcn)

namespace Step

variable {s₁ s₂ : State α}

notation s₁:max " ⇓ᵢ " s₂:max => Step s₁ s₂

def rcn : (s₁ ⇓ᵢ s₂) → ID
  | skip (rcn := rcn) .. | exec (rcn := rcn) .. => rcn

def allows_rcn : (e : s₁ ⇓ᵢ s₂) → s₁.Allows e.rcn
  | skip h .. | exec h .. => h

end Step

-- TODO: Rename this to "Sequence" or something like that.
inductive Execution : State α → State α → Type
  | single : (s₁ ⇓ᵢ s₂) → Execution s₁ s₂
  | trans  : (s₁ ⇓ᵢ s₂) → (Execution s₂ s₃) → Execution s₁ s₃

notation s₁:max " ⇓ᵢ+ " s₂:max => Execution s₁ s₂

def Execution.rcns {s₁ s₂ : State α} : (s₁ ⇓ᵢ+ s₂) → List ID
  | single e => [e.rcn]
  | trans hd tl => hd.rcn :: tl.rcns

structure ClosedExecution (s₁ s₂ : State α) where  
  exec   : s₁ ⇓ᵢ+ s₂
  closed : s₂.Closed
  
notation s₁:max " ⇓| " s₂:max => ClosedExecution s₁ s₂

abbrev ClosedExecution.rcns {s₁ s₂ : State α} (e : s₁ ⇓| s₂) : List ID :=
  e.exec.rcns

end Instantaneous

inductive Advance : State α → State α → Prop 
  | intro (closed : s.Closed) (next : s.NextTag g) (refreshed : Refresh s.rtr ref $ s.actions g) :
    Advance s { s with rtr := ref, tag := g, progress := ∅ }

notation s₁:max " ⇓- " s₂:max => Advance s₁ s₂

inductive Step (s₁ s₂ : State α) : Prop
  | close   (step : s₁ ⇓| s₂)
  | advance (step : s₁ ⇓- s₂)

notation s₁:max " ⇓ " s₂:max => Step s₁ s₂

end Execution

open Execution

inductive Execution : State α → State α → Prop
  | refl : Execution s s
  | step : (s₁ ⇓ s₂) → (Execution s₂ s₃) → Execution s₁ s₃

notation s₁ " ⇓* " s₂ => Execution s₁ s₂