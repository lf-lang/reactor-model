import ReactorModel.Execution.Basic
variable {ι υ} [Value υ]

-- This file defines (and proves) determinism for the reactor model.
-- Determinism can be understood in multiple ways.
-- Primarily, we say the execution is deterministic if there is always ot most one timed
-- step that can be taken.
namespace Execution

theorem ChangeStep.eq_prios {σ₁ σ₂ : Reactor ι υ} {c : Change ι υ} {g : Time.Tag} :
  σ₁ -[c, g]→ σ₂ → σ₁.prios = σ₂.prios := by
  intro h; cases h <;> simp only <;> (apply Reactor.Update.eq_prios; assumption)

theorem ChangeStep.eq_rcns {σ₁ σ₂ : Reactor ι υ} {c : Change ι υ} {g : Time.Tag} :
  σ₁ -[c, g]→ σ₂ → σ₁.rcns = σ₂.rcns := by
  intro h; cases h <;> simp only <;> (apply Reactor.Update.ne_cmp_and_ne_rtr_eq Cmp.rcn; assumption; all_goals { by_contra; contradiction })

theorem InstExecution.preserves_time {σ₁ σ₂ : Reactor ι υ} {ctx₁ ctx₂ : Context ι} :
  (σ₁, ctx₁) ⇓ᵢ+ (σ₂, ctx₂) → ctx₁.time = ctx₂.time := by
  intro h
  induction h
  case single h => cases h <;> simp [Context.addCurrentExecuted_same_time]
  case trans ctx₁ ctx₂ _ h₁₂ h₂₃ hi => 
    have ht : ctx₁.time = ctx₂.time := by cases h₁₂ <;> simp [Context.addCurrentExecuted_same_time]
    simp [hi, ht]

theorem InstExecution.preserves_ctx_past_future {σ₁ σ₂ : Reactor ι υ} {ctx₁ ctx₂ : Context ι} (h : (σ₁, ctx₁) ⇓ᵢ+ (σ₂, ctx₂)) :
  ∀ g, g ≠ ctx₁.time → ctx₁.executedRcns g = ctx₂.executedRcns g := by
  intro g hg
  induction h
  case single h => cases h <;> simp [Context.addCurrentExecuted, Finmap.update_ne]
  case trans ctx₁ ctx₂ ctx₃ he he' hi =>
    have hc : ctx₁.executedRcns g = ctx₂.executedRcns g := by cases he <;> simp [Context.addCurrentExecuted, Finmap.update_ne]
    rw [InstExecution.preserves_time $ single he] at hg
    simp [hc, hi hg]

-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
theorem InstExecution.deterministic {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx' : Context ι} : 
  (σ, ctx) ⇓ᵢ+ (σ₁, ctx') → (σ, ctx) ⇓ᵢ+ (σ₂, ctx') → σ₁ = σ₂ := sorry

theorem StuckInstExecution.ctx_current_complete {σ₁ σ₂ : Reactor ι υ} {ctx₁ ctx₂ : Context ι} :
  (σ₁, ctx₁) ⇓ᵢ| (σ₂, ctx₂) → ctx₂.executedRcns ctx₁.time = σ₁.rcns.ids := by
  intro h
  have ht : ctx₁.time = ctx₂.time := InstExecution.preserves_time h.exec
  have hr : σ₁.rcns = σ₂.rcns := sorry
  rw [ht, hr]
  sorry -- This is probably non-trivial.

theorem StuckInstExecution.eq_ctx {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂ : Context ι} :
  (σ, ctx) ⇓ᵢ| (σ₁, ctx₁) → (σ, ctx) ⇓ᵢ| (σ₂, ctx₂) → ctx₁ = ctx₂ := by
  intro hs₁ hs₂
  apply Context.ext_iff.mpr; apply Finmap.ext
  intro g
  by_cases hg : g = ctx.time
  case pos => simp [hg, hs₁.ctx_current_complete, hs₂.ctx_current_complete]
  case neg => simp [←hs₁.exec.preserves_ctx_past_future g hg, hs₂.exec.preserves_ctx_past_future g hg]

theorem StuckInstExecution.convergent {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂ : Context ι} :
  (σ, ctx) ⇓ᵢ| (σ₁, ctx₁) → (σ, ctx) ⇓ᵢ| (σ₂, ctx₂) → σ₁ = σ₂ := by
  intro hs₁ hs₂
  rw [←StuckInstExecution.eq_ctx hs₁ hs₂] at hs₂
  exact InstExecution.deterministic hs₁.exec hs₂.exec
  
-- The set of reactions can change because of mutations.
-- However, these changes are deterministic.
--lemma networkChangeDeterministic {σ₁ σ₂ σ₁' σ₂' : Reactor ι υ}
--{ctx₁ ctx₂ ctx₁' ctx₂'  : Context ι} :
--  (σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁') →
--  (σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂') →
--  sameReactionExecuted ((σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁')) ((σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) →
--  sameReactionTopologyChanges ((σ₁, ctx₁) ⇓ᵢ (σ₁', ctx₁')) ((σ₂, ctx₂) ⇓ᵢ (σ₂', ctx₂')) :=
--  sorry
lemma inst_convergent_topology {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂  : Context ι} :
    (σ, ctx) ⇓ᵢ| (σ₁, ctx₁) →
    (σ, ctx) ⇓ᵢ| (σ₂, ctx₂) →
    σ₁.rcns.ids = σ₂.rcns.ids := by 
    sorry -- will surely need networkChangeDeterministic (and that should be made to work, too)

theorem Execution.timed_deterministic {σ σ₁ σ₂ : Reactor ι υ} {ctx ctx₁ ctx₂ : Context ι} : 
  (σ, ctx) ⇓ (σ₁, ctx₁) → (σ, ctx) ⇓ (σ₂, ctx₂) → σ₁ = σ₂ := by
  intro he₁ he₂
  cases he₁ <;> cases he₂
  case instToStuck.instToStuck hs₁ hs₂ => exact StuckInstExecution.convergent hs₁ hs₂
  case advanceTime.advanceTime h₁ _ _ _ _ _ h₂ => exact Reactor.eqWithClearedPortsUnique h₁ h₂
  -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Collapse.20cases
  case instToStuck.advanceTime hs _ _ _ _ hr _ => 
    cases hs.exec 
    case single hi =>
      cases hi <;> (
        have := mt (Finset.ext_iff.mp hr _).mpr <| (by assumption)
        have := Finmap.ids_def'.mpr ⟨_, Eq.symm (by assumption)⟩
        contradiction
      )
    case trans _ hi _ => 
      cases hi <;> (
        have := mt (Finset.ext_iff.mp hr _).mpr <| (by assumption)
        have := Finmap.ids_def'.mpr ⟨_, Eq.symm (by assumption)⟩
        contradiction
      )
  case advanceTime.instToStuck _ _ _ _ hr _ hs => 
    cases hs.exec 
    case single hi =>
      cases hi <;> (
        have := mt (Finset.ext_iff.mp hr _).mpr <| (by assumption)
        have := Finmap.ids_def'.mpr ⟨_, Eq.symm (by assumption)⟩
        contradiction
      )
    case trans _ hi _ => 
      cases hi <;> (
        have := mt (Finset.ext_iff.mp hr _).mpr <| (by assumption)
        have := Finmap.ids_def'.mpr ⟨_, Eq.symm (by assumption)⟩
        contradiction
      )

end Execution