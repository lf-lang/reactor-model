import ReactorModel.Execution.Context

structure Execution.State where
  rtr : Reactor
  ctx : Context

namespace Execution.State 

structure isNextTag (s : State) (g : Time.Tag) : Prop where
  mem : g ∈ s.rtr.scheduledTags
  lower : s.ctx.time < g
  upper : ∀ g' ∈ s.rtr.scheduledTags, s.ctx.time < g' → g ≤ g'

theorem isNextTag_unique {s : State} {g₁ g₂ : Time.Tag} :
  (s.isNextTag g₁) → (s.isNextTag g₂) → g₁ = g₂ :=
  sorry

end Execution.State 