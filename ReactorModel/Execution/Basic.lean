import ReactorModel.Execution.State

open Classical Reactor Execution State

variable [Hierarchical α]

namespace Execution
namespace Step

inductive Apply : Change α✦ → State α → State α → Type
  | inp {rtr} : (LawfulUpdate .inp i v s.rtr rtr) → Apply (.inp i v) s { s with rtr }
  | out {rtr} : (LawfulUpdate .out i v s.rtr rtr) → Apply (.out i v) s { s with rtr }
  | stv {rtr} : (LawfulUpdate .stv i v s.rtr rtr) → Apply (.stv i v) s { s with rtr }
  | act : Apply (.act i t v ) s (s.schedule i t v)
  | mut : Apply (.mut _) s s -- Mutations are currently no-ops.

notation s₁:max " -[" c "]→ " s₂:max => Apply c s₁ s₂

inductive Apply.RTC : Reaction.Output α✦ → State α → State α → Type
  | refl  : Apply.RTC [] s s
  | trans : (s₁ -[hd]→ s₂) → (Apply.RTC tl s₂ s₃) → Apply.RTC (hd :: tl) s₁ s₃

notation s₁:max " -[" cs "]→ " s₂:max => Apply.RTC cs s₁ s₂

inductive Skip : State α → State α → Type
  | mk : (Allows s rcn) → (¬Triggers s rcn) → Skip s (s.record rcn)

notation s₁:max " ↓ₛ " s₂:max => Skip s₁ s₂

inductive Exec : State α → State α → Type
  | mk : (Allows s₁ rcn) → (Triggers s₁ rcn) → (s₁ -[s₁.output rcn]→ s₂) → Exec s₁ (s₂.record rcn)

notation s₁:max " ↓ₑ " s₂:max => Exec s₁ s₂

inductive Time : State α → State α → Type
  | mk : (Closed s) → (NextTag s g) → (Refresh s.rtr ref <| s.actions g) →
         Time s { s with rtr := ref, tag := g, progress := ∅ }

notation s₁:max " ↓ₜ " s₂:max => Time s₁ s₂

end Step

inductive Step (s₁ s₂ : State α) : Type
  | skip (s : s₁ ↓ₛ s₂)
  | exec (e : s₁ ↓ₑ s₂)
  | time (t : s₁ ↓ₜ s₂)

end Execution

-- An execution trace connecting two given states.
inductive Execution : State α → State α → Type
  | refl  : Execution s s
  | trans : (Step s₁ s₂) → (Execution s₂ s₃) → Execution s₁ s₃
