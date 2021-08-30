import ReactorModel.Primitives

open Reactor
open Reactor.Ports

variable (ι υ) [ID ι] [Value υ]

structure Reaction :=
  (deps : Ports.Role → Finset ι) 
  (triggers : Finset ι)
  (body : Ports ι υ → StateVars ι υ → (Ports ι υ × StateVars ι υ))
  (tsSubInDeps : triggers ⊆ deps Role.in)
  (inDepOnly : ∀ {i i'} s, (i =[deps Role.in] i') → body i s = body i' s)
  (outDepOnly : ∀ i s {o}, (o ∉ deps Role.out) → (body i s).fst[o] = none)

namespace Reaction

variable {ι υ}

instance : CoeFun (Reaction ι υ) (λ _ => Ports ι υ → StateVars ι υ → (Ports ι υ × StateVars ι υ)) where
  coe rcn := rcn.body

theorem outPrtValsSubOutDeps (rcn : Reaction ι υ) (p : Ports ι υ) (s : StateVars ι υ) :
  (rcn i s).fst.inhabitedIDs ⊆ rcn.deps Role.out := by
  simp only [Finset.subset_iff]
  intro o
  rw [←not_imp_not]
  intro h
  have hₙ := rcn.outDepOnly i s h
  exact Ports.inhabitedIDsNone hₙ

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
