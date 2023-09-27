import ReactorModel.Execution.State

open Classical Reactor Execution State

variable [Hierarchical α]

namespace Execution
namespace Step 

inductive Apply : Change → State α → State α → Type
  | inp {rtr} : (LawfulUpdate .inp i v s.rtr rtr) → Apply (.inp i v) s { s with rtr }    
  | out {rtr} : (LawfulUpdate .out i v s.rtr rtr) → Apply (.out i v) s { s with rtr }    
  | stv {rtr} : (LawfulUpdate .stv i v s.rtr rtr) → Apply (.stv i v) s { s with rtr }    
  | act : Apply (.act i t v ) s (s.schedule .log i t v)
  | mut : Apply (.mut _) s s -- Mutations are currently no-ops.
  
notation s₁:max " -[" c "]→ " s₂:max => Apply c s₁ s₂

inductive Apply.RTC : Reaction.Output → State α → State α → Type
  | refl  : Apply.RTC [] s s
  | trans : (s₁ -[hd]→ s₂) → (Apply.RTC tl s₂ s₃) → Apply.RTC (hd :: tl) s₁ s₃  

notation s₁:max " -[" cs "]→ " s₂:max => Apply.RTC cs s₁ s₂

inductive Skip : State α → State α → Type
  | mk : (Allows s rcn) → (¬Triggers s rcn) → (s.clock ≤ t) → Skip s (s.record rcn |>.at t)

notation s₁:max " ↓ˢ " s₂:max => Skip s₁ s₂

inductive Exec : State α → State α → Type
  | mk : (Allows s₁ rcn) → (Triggers s₁ rcn) → (s₁ -[s₁.output rcn]→ s₂) → (s₁.clock ≤ t) → 
         Exec s₁ (s₂.record rcn |>.at t)

notation s₁:max " ↓ᵉ " s₂:max => Exec s₁ s₂

inductive Tag : State α → State α → Type
  | mk : (Closed s) → (NextTag s g) → (Refresh s.rtr ref $ s.logicals g) → (g.time ≤ t) → 
         (s.clock ≤ t) → Tag s { s with rtr := ref, tag := g, clock := t, progress := ∅ }

notation s₁:max " ↓ᵗ " s₂:max => Tag s₁ s₂

inductive Clock : State α → State α → Type
  | mk : (s.clock < t) → Clock s (s.at t)  

notation s₁:max " ↓ᶜ " s₂:max => Clock s₁ s₂

-- TODO: Rename this to `Tick`?
inductive Sync (s₁ s₂ : State α)
  | skip  (s : s₁ ↓ˢ s₂)
  | exec  (e : s₁ ↓ᵉ s₂)
  | tag   (t : s₁ ↓ᵗ s₂)
  | clock (c : s₁ ↓ᶜ s₂)

end Step

-- TODO: I'm inclined to remove the notion of a `clock` step and intepret each of the remaining sync
--       steps as meaning "somewhere in the physical time span s₁.clock to s₂.clock the step was
--       performed". The only problem with removing the `clock` step is that we can only schedule
--       physical actions in parallel to *some* sync step existing. Is this a problem? I think the 
--       answer might be related to how termination of reactors works in a setting where we have
--       physical time. Cause wouldnt such a reactor never terminate, as there might still be a
--       physical action scheduled at some point in the future.
--       Side Note: If you remove `clock` step, rename the `Sync` steps back to `Logical` and 
--                  have the indices be subscripts.

inductive Step : State α → State α → Type
  | sync : (Step.Sync s₁ s₂) → Step s₁ s₂
  | phys : (Step.Sync s₁ s₂) → (i ∈ s₁.rtr[.phy]) → (s₁.clock ≤ t) → (t ≤ s₂.clock) → 
            Step s₁ (s₂.schedule .phy i t v)

notation s₁:max " ↓ " s₂:max => Step s₁ s₂

end Execution

inductive Execution : State α → State α → Type
  | refl  : Execution s s
  | trans : (s₁ ↓ s₂) → (Execution s₂ s₃) → Execution s₁ s₃

notation s₁ " ↓* " s₂ => Execution s₁ s₂

-- TODO: Would it be nice/useful to have a notion of events?
--       Perhaps `Change`s are something like "instantaneous events"?

-- TODO: Move this to Theorems/Execution.lean once that file builds again.
-- TODO: If a list is impractical to work with, you could also return a map Time ⇀ (ID × Value).
noncomputable def Execution.physicalEvents {s₁ : State α} : (s₁ ↓* s₂) → List (Time × ID × Value) 
  | refl => []
  | trans (.sync _) tl => tl.physicalEvents
  | trans (.phys (t := t) (i := i) (v := v) ..) tl => (t, i, v) :: tl.physicalEvents