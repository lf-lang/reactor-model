import ReactorModel.Components.Change

open Ports

variable (ι υ) [ID ι] [Value υ]

structure Reaction where
  deps :        Ports.Role → Finset ι 
  triggers :    Finset ι
  body :        Ports ι υ → StateVars ι υ → List (Change ι υ)
  tsSubInDeps : triggers ⊆ deps Role.in
  inDepOnly :   ∀ {i i'} s, (i =[deps Role.in] i') → (body i s = body i' s)
  outDepOnly :  ∀ i s {o} (v : υ), (o ∉ deps Role.out) → (Change.port o v) ∉ (body i s)

variable {ι υ}

-- A non-`Raw` accessor for a `Reactor`'s mutations.
-- This uses the constraints given by `Reactor.wf` in order to convert `Raw.Reaction`s to `Reaction`s.
def Reactor.rcns (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  let raw : Finmap ι (Raw.Reaction ι υ) := {lookup := rtr.raw.rcns, finite := rtr.wf.rcnsFinite}
  raw.map (λ rcn => {
      deps := rcn.deps,
      triggers := rcn.triggers,
      body := (λ p s => (rcn.body p s).map (λ c => sorry)),
      tsSubInDeps := sorry,
      inDepOnly := sorry,
      outDepOnly := sorry
    }
  )

variable {ι υ}

namespace Reaction

-- A coercion so that reactions can be called directly as functions.
instance : CoeFun (Reaction ι υ) (λ _ => Ports ι υ → StateVars ι υ → (List (Change ι υ))) where
  coe rcn := rcn.body

def isNorm (rcn : Reaction ι υ) : Prop :=
  ∀ i s c, c ∈ (rcn i s) → ¬c.mutates

def isMut (rcn : Reaction ι υ) : Prop := ¬rcn.isNorm

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

noncomputable def Reactor.norms (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isNorm)

noncomputable def Reactor.muts (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isMut)