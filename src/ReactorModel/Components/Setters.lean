import ReactorModel.Components.Getters

open Ports

variable {ι υ} [ID ι] [Value υ]

namespace Reaction

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

end Reaction

namespace Reactor

def update (σ₁ σ₂ : Reactor ι υ) (cmp : Cmp) (i : ι) (v : cmp.type ι υ) : Prop := sorry
-- Needs recursion:
/-
  match σ₁ & i with
  | none => False
  | some p => 
    if p = ⊤
    then directUpdate σ₁ σ₂ cmp i v
    else
      σ₁.ports = σ₂.ports ∧ σ₂.roles = σ₁.roles ∧ σ₂.state = σ₁.state ∧ σ₂.prios = σ₁.prios ∧ σ₂.rcns = σ₁.rcns ∧ 
      ∀ σₚ ∈ σ₁.nest.entries, 
        if σₚ.snd & i = none
        then σₚ ∈ σ₂.nest.entries
        else update σₚ.snd σ₂ cmp i v
where
  directUpdate (σ₁ σ₂ : Reactor ι υ) (cmp : Cmp) (i : ι) (v : cmp.type ι υ) : Prop :=
    match cmp with 
      | Cmp.prt => sorry
        σ₂.ports = (σ₁.ports.update i v) ∧ 
        σ₂.roles = σ₁.roles ∧ σ₂.state = σ₁.state ∧ σ₂.nest = σ₁.nest ∧ σ₂.prios = σ₁.prios ∧ σ₂.rcns = σ₁.rcns
      | Cmp.rtr => sorry
        σ₂.nest = (σ₁.nest.update i v) ∧ 
        σ₂.ports = σ₁.ports ∧ σ₂.roles = σ₁.roles ∧ σ₂.state = σ₁.state ∧ σ₂.prios = σ₁.prios ∧ σ₂.rcns = σ₁.rcns
      | Cmp.stv => sorry
        σ₂.state = (σ₁.state.update i v) ∧ 
        σ₂.ports = σ₁.ports ∧ σ₂.roles = σ₁.roles ∧ σ₂.nest = σ₁.nest ∧ σ₂.prios = σ₁.prios ∧ σ₂.rcns = σ₁.rcns
      | Cmp.rcn => sorry
        σ₂.rcns = (σ₁.rcns.update i v) ∧ 
        σ₂.ports = σ₁.ports ∧ σ₂.roles = σ₁.roles ∧ σ₂.state = σ₁.state ∧ σ₂.nest = σ₁.nest ∧ σ₂.prios = σ₁.prios
-/

notation σ₁:max " -[" c ", " i " := " v "]→ " σ₂:max => Reactor.update σ₁ σ₂ c i v

end Reactor
