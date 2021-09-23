import ReactorModel.Components.RcnOutput

open Ports

variable (ι υ) [ID ι] [Value υ]

structure Reaction where
  isMut :       Bool
  deps :        Ports.Role → Finset ι 
  triggers :    Finset ι
  body :        Ports ι υ → StateVars ι υ → RcnOutput ι υ
  tsSubInDeps : triggers ⊆ deps Role.in
  inDepOnly :   ∀ {i i'} s, (i =[deps Role.in] i') → body i s = body i' s
  outDepOnly :  ∀ i s {o}, (o ∉ deps Role.out) → (body i s).prtVals[o] = none 
  normDelCns :  ¬isMut → ∀ i s, (body i s).delCns  = []
  normDelRtrs : ¬isMut → ∀ i s, (body i s).delRtrs = []
  normNewCns :  ¬isMut → ∀ i s, (body i s).newCns  = []
  normNewRtrs : ¬isMut → ∀ i s, (body i s).newRtrs = []

variable {ι υ}

-- A non-`Raw` accessor for a `Reactor`'s mutations.
-- This uses the constraints given by `Reactor.wf` in order to convert `Raw.Reaction`s to `Reaction`s.
def Reactor.rcns (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  let raw : Finmap ι (Raw.Reaction ι υ) := {lookup := rtr.raw.rcns, finite := rtr.wf.rcnsFinite}
  raw.map (λ rcn => {
      isMut := rcn.isMut,
      deps := rcn.deps,
      triggers := rcn.triggers,
      body := (λ p s => {
          prtVals := (rcn.body p s).prtVals,
          state   := (rcn.body p s).state,
          newCns  := (rcn.body p s).newCns,
          delCns  := (rcn.body p s).delCns,
          newRtrs := (rcn.body p s).newRtrs.map (λ r => {
              raw := r,
              wf := sorry 
            }
          ),
          delRtrs := (rcn.body p s).delRtrs,
        }
      ),
      tsSubInDeps := sorry,
      inDepOnly := sorry,
      outDepOnly := sorry,
      normDelCns := sorry,
      normDelRtrs := sorry,
      normNewCns := sorry,
      normNewRtrs := sorry
    }
  )

namespace Reaction

variable {ι υ}

-- A coercion so that reactions can be called directly as functions.
instance : CoeFun (Reaction ι υ) (λ _ => Ports ι υ → StateVars ι υ → (RcnOutput ι υ)) where
  coe rcn := rcn.body

theorem outPrtValsSubOutDeps (rcn : Reaction ι υ) (p : Ports ι υ) (s : StateVars ι υ) :
  (rcn i s).prtVals.inhabitedIDs ⊆ rcn.deps Role.out := by
  simp only [Finset.subset_iff]
  intro o
  rw [←not_imp_not]
  intro h
  have hₙ := rcn.outDepOnly i s h
  exact Ports.inhabitedIDsNone hₙ

-- The condition under which a given reaction triggers on a given (input) port-assignment.
def triggersOn (rcn : Reaction ι υ) (p : Ports ι υ) : Prop :=
  ∃ (t : ι) (v : υ), t ∈ rcn.triggers ∧ p[t] = some v

theorem eqInputEqTriggering {rcn : Reaction ι υ} {p₁ p₂ : Ports ι υ} (h : p₁ =[rcn.deps Role.in] p₂) :
  rcn.triggersOn p₁ ↔ rcn.triggersOn p₂ := by
  simp [triggersOn, Ports.eqAt] at h ⊢
  split
  allGoals {
    intro hₑ
    match hₑ with
    | ⟨t, r, ⟨v, h'⟩⟩ =>
      exists t
      exists r
      exists v
      have hₜ := Finset.mem_of_subset rcn.tsSubInDeps r
      have h := eqLookupEqGet (h t hₜ)
      simp [←h', h]
  }

end Reaction