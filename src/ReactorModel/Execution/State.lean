import ReactorModel.Execution.Context

structure Execution.State (ι υ) [Value υ] where
  rtr : Reactor ι υ
  ctx : Context ι

namespace Execution.State 

variable {ι υ} [Value υ]

structure isNextTag (s : State ι υ) (g : Time.Tag) : Prop where
  mem : g ∈ s.rtr.scheduledTags
  lower : s.ctx.time < g
  upper : ∀ g' ∈ s.rtr.scheduledTags, s.ctx.time < g' → g ≤ g'

theorem isNextTag_unique {s : State ι υ} {g₁ g₂ : Time.Tag} :
  (s.isNextTag g₁) → (s.isNextTag g₂) → g₁ = g₂ :=
  sorry

end Execution.State 