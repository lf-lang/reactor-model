import ReactorModel.Components.Change

open Ports
open Classical

variable (ι υ) [ID ι] [Value υ]

structure Reaction where
  deps :        Ports.Role → Finset ι 
  triggers :    Finset ι
  children :    Finset ι
  body :        Ports ι υ → StateVars ι υ → List (Change ι υ)
  tsSubInDeps : triggers ⊆ deps Role.in
  outDepOnly :  ∀ p s {o} (v : υ), (o ∉ deps Role.out) → (Change.port o v) ∉ (body p s)
  normNoChild : (∀ i s c, c ∈ (body i s) → ¬c.mutates) → children = ∅

variable {ι υ}

-- A non-`Raw` accessor for a `Reactor`'s mutations.
-- This uses the constraints given by `Reactor.wf` in order to convert `Raw.Reaction`s to `Reaction`s.
def Reactor.rcns (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  let raw : Finmap ι (Raw.Reaction ι υ) := {lookup := rtr.raw.rcns, finite := rtr.wf.direct.rcnsFinite}
  raw.map' (λ rcn h => {
      deps := rcn.deps,
      triggers := rcn.triggers,
      children := rcn.children,
      body := (λ p s => (rcn.body p s).map (λ c => 
        sorry
      )),
      tsSubInDeps := sorry,
      outDepOnly := by
        intro h'
        have hw := (rtr.wf.direct.rcnsWF (Finmap.values_def.mp h)).outDepOnly
        intro s o v ho
        sorry
      ,
      normNoChild := by
        intro h'
        have hw := (rtr.wf.direct.rcnsWF (Finmap.values_def.mp h)).normNoChild
        simp at h'
        simp [Raw.Reaction.isNorm] at hw
        suffices hg : ∀ i s c, c ∈ Raw.Reaction.body rcn i s → ¬Raw.Change.mutates c from hw hg
        intro i s c hc
        sorry
        -- exact h' i s c hc
    }
  )

variable {ι υ}

namespace Reaction

-- A coercion so that reactions can be called directly as functions.
instance : CoeFun (Reaction ι υ) (λ _ => Ports ι υ → StateVars ι υ → (List (Change ι υ))) where
  coe rcn := rcn.body

-- A reaction is normal ("norm") if its body produces no mutating changes.
def isNorm (rcn : Reaction ι υ) : Prop :=
  ∀ i s c, c ∈ (rcn i s) → ¬c.mutates

def isMut (rcn : Reaction ι υ) : Prop := ¬rcn.isNorm

-- A relay reaction that connects a `src` port with a `dst` port.
def relay (src dst : ι) : Reaction ι υ := {
  deps := λ r => match r with | Role.in => Finset.singleton src | Role.out => Finset.singleton dst,
  triggers := Finset.singleton src,
  children := ∅,
  body := λ p _ => match p[src] with | none => [] | some v => [Change.port dst v],
  tsSubInDeps := by simp,
  outDepOnly := by
    intro p _ o v h hc
    simp at *
    cases hs : p[src]
    case none => simp [hs] at *
    case some v' =>
      simp [hs] at *
      rw [Finset.not_mem_singleton] at h
      have hc' := hc.left
      contradiction
  normNoChild := by simp
}

noncomputable def updateInDeps {rcn : Reaction ι υ} {is : Finset ι} : Reaction ι υ := 
  let deps' := Function.update rcn.deps Role.in is
  {
    deps := deps',
    triggers := rcn.triggers ∩ (deps' Role.in), 
    children := rcn.children,
    body := rcn.body,
    tsSubInDeps := Finset.inter_subset_right _ _,
    outDepOnly := λ i s _ v h' => rcn.outDepOnly i s v h',
    normNoChild := rcn.normNoChild
  }

noncomputable def updateOutDeps {rcn : Reaction ι υ} {is : Finset ι} (h : ∀ i s {o} (v : υ), (o ∉ is) → (Change.port o v) ∉ rcn i s) : Reaction ι υ := 
  let deps' := Function.update rcn.deps Role.out is
  {
    deps := deps',
    triggers := rcn.triggers ∩ (deps' Role.in), 
    children := rcn.children,
    body := rcn.body,
    tsSubInDeps := Finset.inter_subset_right _ _,
    outDepOnly := λ i s _ v h' => h i s v h',
    normNoChild := rcn.normNoChild
  } 

noncomputable def updateTriggers {rcn : Reaction ι υ} {is : Finset ι} (h : is ⊆ rcn.deps Role.in) : Reaction ι υ := {
  deps := rcn.deps,
  triggers := is, 
  children := rcn.children,
  body := rcn.body,
  tsSubInDeps := h,
  outDepOnly := rcn.outDepOnly,
  normNoChild := rcn.normNoChild
}

noncomputable def updateChildren {rcn : Reaction ι υ} (is : Finset ι) (h : rcn.isMut) : Reaction ι υ := {
  deps := rcn.deps,
  triggers := rcn.triggers, 
  children := is,
  body := rcn.body,
  tsSubInDeps := rcn.tsSubInDeps,
  outDepOnly := rcn.outDepOnly,
  normNoChild := by
    simp only [isMut, isNorm] at h
    intro h'
    contradiction
}

-- The condition under which a given reaction triggers on a given (input) port-assignment.
def triggersOn (rcn : Reaction ι υ) (p : Ports ι υ) : Prop :=
  ∃ (t : ι) (v : υ), t ∈ rcn.triggers ∧ p[t] = some v

theorem eq_input_eq_triggering {rcn : Reaction ι υ} {p₁ p₂ : Ports ι υ} (h : p₁ =[rcn.deps Role.in] p₂) :
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
      simp [←h', (h t hₜ)]
  }

end Reaction

noncomputable def Reactor.norms (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isNorm)

noncomputable def Reactor.muts (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isMut)