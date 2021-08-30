import ReactorModel.Components.MutOutput

open Reactor
open Reactor.Ports

variable (ι υ) [ID ι] [Value υ]

structure Mutation where
  deps : Ports.Role → Finset ι 
  triggers : Finset ι
  body : Ports ι υ → StateVars ι υ → MutOutput ι υ
  tsSubInDeps : triggers ⊆ deps Role.in
  inDepOnly : ∀ {i i'} s, (i =[deps Role.in] i') → body i s = body i' s
  outDepOnly : ∀ i s {o}, (o ∉ deps Role.out) → (body i s).prtVals[o] = none 

variable {ι υ}

def Reactor.muts (rtr : Reactor ι υ) : ι ▸ Mutation ι υ :=
  let raw : Finmap ι (Raw.Mutation ι υ) := {lookup := rtr.raw.muts, finite := rtr.wf.mutsFinite}
  raw.map (λ m => {
      deps := m.deps,
      triggers := m.triggers,
      body := (λ p s => {
          prtVals := (m.body p s).prtVals,
          state   := (m.body p s).state,
          newCns  := (m.body p s).newCns,
          delCns  := (m.body p s).delCns,
          newRtrs := (m.body p s).newRtrs.map (λ r => {
              raw := r,
              wf := sorry 
            }
          ),
          delRtrs := (m.body p s).delRtrs,
        }
      ),
      tsSubInDeps := sorry,
      inDepOnly := sorry,
      outDepOnly := sorry
    }
  )

namespace Mutation

instance : CoeFun (Mutation ι υ) (λ _ => Ports ι υ → StateVars ι υ → MutOutput ι υ) where
  coe m := m.body

theorem outPrtValsSubOutDeps (m : Mutation ι υ) (p : Ports ι υ) (s : StateVars ι υ) :
  (m i s).prtVals.inhabitedIDs ⊆ m.deps Role.out := by
  simp only [Finset.subset_iff]
  intro o
  rw [←not_imp_not]
  intro h
  have hₙ := m.outDepOnly i s h
  exact Ports.inhabitedIDsNone hₙ

def triggersOn (m : Mutation ι υ) (p : Ports ι υ) : Prop :=
  ∃ (t : ι) (v : υ), t ∈ m.triggers ∧ p[t] = some v

theorem eqInputEqTriggering {m : Mutation ι υ} {p₁ p₂ : Ports ι υ} (h : p₁ =[m.deps Role.in] p₂) :
  m.triggersOn p₁ ↔ m.triggersOn p₂ := by
  simp [triggersOn, Ports.eqAt] at h ⊢
  split
  allGoals {
    intro hₑ
    match hₑ with
    | ⟨t, r, ⟨v, h'⟩⟩ =>
      exists t
      exists r
      exists v
      have hₜ := Finset.mem_of_subset m.tsSubInDeps r
      have h := eqLookupEqGet (h t hₜ)
      simp [←h', h]
  }

end Mutation