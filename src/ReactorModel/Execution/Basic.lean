import ReactorModel.Execution.Context

variable {ι υ} [Value υ]

namespace Execution

inductive ChangeStep (g : Time.Tag) (σ₁ σ₂ : Reactor ι υ) : Change ι υ → Prop 
  | port {i v} : (σ₁ -[Cmp.prt, i := v]→ σ₂) → ChangeStep g σ₁ σ₂ (Change.port i v) -- Port propagation isn't necessary/possible, because we're using relay reactions. 
  | state {i v} : (σ₁ -[Cmp.stv, i := v]→ σ₂) → ChangeStep g σ₁ σ₂ (Change.state i v)
  | action {i} {t : Time} {tg : Time.Tag} {v : υ} {a : Time.Tag ▸ υ} : 
    (σ₁.acts i = a) → 
    (t.after g = tg) → 
    (σ₁ -[Cmp.act, i := a.update tg v]→ σ₂) → 
    ChangeStep g σ₁ σ₂ (Change.action i t v)

notation σ₁:max " -[" c ", " g "]→ " σ₂:max => ChangeStep g σ₁ σ₂ c

inductive ChangeListStep (g : Time.Tag) : Reactor ι υ → Reactor ι υ → List (Change ι υ) → Prop
  | nil (σ₁) : ChangeListStep g σ₁ σ₁ []
  | cons {σ₁ σ₂ σ₃ change rest} : (σ₁ -[change, g]→ σ₂) → (ChangeListStep g σ₂ σ₃ rest) → ChangeListStep g σ₁ σ₃ (change::rest)

notation σ₁:max " -[" cs ", " g "]→* " σ₂:max => ChangeListStep g σ₁ σ₂ cs

inductive Step (σ₁ : Reactor ι υ) (ctx₁ : Context ι) (σ₂ : Reactor ι υ) : Context ι → Prop 
  | execReaction {rcn : Reaction ι υ} {i} : 
    (σ₁.rcns i = rcn) →
    (σ₁.predecessors i ⊆ ctx₁.currentExecutedRcns) →
    (i ∉ ctx₁.currentExecutedRcns) →
    (rcn.triggersOn $ σ₁.inputForRcn rcn ctx₁.time) →
    (σ₁ -[rcn $ σ₁.inputForRcn rcn ctx₁.time, ctx₁.time]→* σ₂) →
    Step σ₁ ctx₁ σ₂ (ctx₁.addCurrentExecuted i)
  | skipReaction {rcn : Reaction ι υ} {i} :
    (σ₁.rcns i = rcn) →
    (σ₁.predecessors i ⊆ ctx₁.currentExecutedRcns) →
    (i ∉ ctx₁.currentExecutedRcns) →
    (¬(rcn.triggersOn $ σ₁.inputForRcn rcn ctx₁.time)) →
    Step σ₁ ctx₁ σ₂ (ctx₁.addCurrentExecuted i)
  | advanceTime {g} (hg : ctx₁.time < g) :
    (g ∈ σ₁.scheduledTags) →
    (∀ g' ∈ σ₁.scheduledTags, ctx₁.time < g' → g ≤ g') →
    (ctx₁.currentExecutedRcns = σ₁.rcns.ids) →
    Step σ₁ ctx₁ σ₂ (ctx₁.advanceTime hg)

notation "(" σ₁ ", " ctx₁ ") ⇓ (" σ₂ ", " ctx₂ ")" => Step σ₁ ctx₁ σ₂ ctx₂

end Execution

open Execution

-- An execution of a reactor model is a series of execution steps.
-- We model this with a reflexive transitive closure:
inductive Execution : Reactor ι υ → Context ι → Reactor ι υ → Context ι → Prop
 | refl (σ ctx) : Execution σ ctx σ ctx
 | step {σ₁ ctx₁ σ₂ ctx₂ σ₃ ctx₃} : (σ₁, ctx₁) ⇓ (σ₂, ctx₂) → Execution σ₂ ctx₂ σ₃ ctx₃ → Execution σ₁ ctx₁ σ₃ ctx₃

notation "(" σ₁ ", " ctx₁ ") ⇓* (" σ₂ ", " ctx₂ ")" => Execution σ₁ ctx₁ σ₂ ctx₂