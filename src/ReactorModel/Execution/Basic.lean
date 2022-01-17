import ReactorModel.Execution.Context

variable {ι υ} [Value υ]

-- TODO: Come up with something nicer.
structure Reactor.eqWithClearedPorts (σ₁ σ₂ : Reactor ι υ) where
  otherCmpsEq : ∀ {cmp}, cmp ≠ Cmp.prt → cmp.accessor σ₁ = cmp.accessor σ₂
  priosEq : σ₁.prios = σ₂.prios
  rolesEq : σ₁.roles = σ₂.roles
  samePortIDs : ∀ i, σ₁.containsID i Cmp.prt ↔ σ₂.containsID i Cmp.prt
  clearedIDs : ∀ i, σ₂.containsID i Cmp.prt → σ₂ *[Cmp.prt, i]= ⊥

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

inductive Step (σ : Reactor ι υ) (ctx : Context ι) : Reactor ι υ → Context ι → Prop 
  | execReaction {rcn : Reaction ι υ} {i σ'} : 
    (σ.rcns i = rcn) →
    (σ.predecessors i ⊆ ctx.currentExecutedRcns) →
    (i ∉ ctx.currentExecutedRcns) →
    (rcn.triggersOn $ σ.inputForRcn rcn ctx.time) →
    (σ -[rcn $ σ.inputForRcn rcn ctx.time, ctx.time]→* σ') →
    Step σ ctx σ' (ctx.addCurrentExecuted i)
  | skipReaction {rcn : Reaction ι υ} {i} :
    (σ.rcns i = rcn) →
    (σ.predecessors i ⊆ ctx.currentExecutedRcns) →
    (i ∉ ctx.currentExecutedRcns) →
    (¬(rcn.triggersOn $ σ.inputForRcn rcn ctx.time)) →
    Step σ ctx σ (ctx.addCurrentExecuted i)
  | advanceTime {σ' g} (hg : ctx.time < g) :
    (g ∈ σ.scheduledTags) →
    (∀ g' ∈ σ.scheduledTags, ctx.time < g' → g ≤ g') →
    (ctx.currentExecutedRcns = σ.rcns.ids) →
    (σ.eqWithClearedPorts σ') →
    Step σ ctx σ' (ctx.advanceTime hg)

notation "(" σ₁ ", " ctx₁ ") ⇓ (" σ₂ ", " ctx₂ ")" => Step σ₁ ctx₁ σ₂ ctx₂

end Execution

open Execution

-- An execution of a reactor model is a series of execution steps.
-- We model this with a reflexive transitive closure:
inductive Execution : Reactor ι υ → Context ι → Reactor ι υ → Context ι → Prop
 | refl (σ ctx) : Execution σ ctx σ ctx
 | step {σ₁ ctx₁ σ₂ ctx₂ σ₃ ctx₃} : (σ₁, ctx₁) ⇓ (σ₂, ctx₂) → Execution σ₂ ctx₂ σ₃ ctx₃ → Execution σ₁ ctx₁ σ₃ ctx₃

notation "(" σ₁ ", " ctx₁ ") ⇓* (" σ₂ ", " ctx₂ ")" => Execution σ₁ ctx₁ σ₂ ctx₂