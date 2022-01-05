import ReactorModel.Components.Change

open Port Classical

variable (ι υ : Type _) [Value υ]

open Reaction

-- Reactions are the components that can produce changes in a reactor system.
-- The can be classified into "normal" reactions and "mutations". The `Reaction`
-- type encompasses both of these flavors (cf. `isNorm` and `isMut`).
--
-- The `deps` field defines both dependencies and antidependencies by referring to
-- the ports' IDs and separating these IDs by the role of the port they refer to.
--
-- A reaction's `triggers` are a subset of its input ports (by `tsSubInDeps`).
-- This field is used to define when a reaction triggers (cf. `triggersOn`).
--
-- The `outDepOnly` represents a constraint on the reaction's `body`.
--
-- The `children` are a concept that only applies to mutations. When mutations
-- produce a `Change.create <reactor> <id>`, they need to remember the `<id>`
-- of the reactor they created (for reasons that are related to the execution model). 
-- These IDs are recorded in their `children` field. Since "normal" reactions can't 
-- create reactors (since this is a mutating change), they can't have children. 
-- This is enforced by `normNoChild` (the condition `∀ i s c, c ∈ (body i s) → ¬c.mutates` 
-- is precisely the definition of `isNorm`, but we couldn't use `isNorm` in the definition 
-- of `Reaction` yet, as this would be circular).
@[ext]
structure Reaction where
  deps :          Port.Role → Finset ι 
  triggers :      Finset ι
  children :      Finset ι
  body :          Input ι υ → List (Change ι υ)
  tsSubInDeps :   triggers ⊆ deps Role.in
  prtOutDepOnly : ∀ i {o} (v : υ),     (o ∉ deps Role.out) → Change.port o v ∉ body i
  actOutDepOnly : ∀ i {o} (t) (v : υ), (o ∉ deps Role.out) → Change.action o t v ∉ body i
  normNoChild :   (∀ i c, (c ∈ body i) → ¬c.mutates) → children = ∅
  
variable {ι υ}

namespace Reaction

-- A coercion so that reactions can be called directly as functions.
-- So when you see something like `rcn p s` that's the same as `rcn.body p s`.
instance : CoeFun (Reaction ι υ) (λ _ => Input ι υ → (List (Change ι υ))) where
  coe rcn := rcn.body

-- A reaction is normal ("norm") if its body produces no mutating changes.
def isNorm (rcn : Reaction ι υ) : Prop :=
  ∀ i c, (c ∈ rcn i) → ¬c.mutates

-- A reaction is a mutation if it is not "normal", i.e. it does produce
-- mutating changes for some input.
def isMut (rcn : Reaction ι υ) : Prop := ¬rcn.isNorm

-- A version of `Reaction.norm_no_child` that uses `isNorm`.
theorem norm_no_child' (rcn : Reaction ι υ) : rcn.isNorm → rcn.children = ∅ := 
  rcn.normNoChild

-- The condition under which a given reaction triggers on a given (input) port-assignment.
def triggersOn (rcn : Reaction ι υ) (i : Input ι υ) : Prop :=
  ∃ t, t ∈ rcn.triggers ∧ i.ports[t] ≠ none

-- TODO: Remove this if it is not used.
theorem eq_input_eq_triggering {rcn : Reaction ι υ} {i₁ i₂ : Input ι υ} (h : i₁.ports =[rcn.deps Role.in] i₂.ports) :
  rcn.triggersOn i₁ ↔ rcn.triggersOn i₂ := by
  simp [triggersOn, Finmap.eqAt] at h ⊢
  apply Iff.intro <;> (
    intro ⟨t, ⟨hm, hn⟩⟩
    exists t
    apply And.intro hm
    have ht := h _ $ Finset.subset_iff.mp rcn.tsSubInDeps hm
    simp [ht] at hn ⊢
    assumption
  )
  
-- Relay reactions are a specific kind of reaction that allow us to simplify what
-- it means for reactors' ports to be connected. We can formalize connections between
-- reactors' ports by creating a reaction that declares these ports and only these
-- ports as dependency and antidependency respectively, and does nothing but relay the
-- value from its input to its output.
noncomputable def relay (src dst : ι) : Reaction ι υ := {
  deps := λ r => match r with | Role.in => Finset.singleton src | Role.out => Finset.singleton dst,
  triggers := Finset.singleton src,
  children := ∅,
  body := λ i => i.ports[src].elim [] ([Change.port dst ·]),
  tsSubInDeps := by simp,
  prtOutDepOnly := by
    intro i o v h hc
    cases hs : i.ports[src] <;> simp [Option.elim, hs] at *
    case some v' =>
      rw [Finset.not_mem_singleton] at h
      have hc' := hc.left
      contradiction
  actOutDepOnly := by
    intro i
    cases hs : i.ports[src] <;> simp [Option.elim, hs]
  normNoChild := by simp
}

-- TODO: Docs

noncomputable def updateInDeps {rcn : Reaction ι υ} {is : Finset ι} : Reaction ι υ := 
  let deps' := Function.update rcn.deps Role.in is
  {
    deps := deps',
    triggers := rcn.triggers ∩ (deps' Role.in), 
    children := rcn.children,
    body := rcn.body,
    tsSubInDeps := Finset.inter_subset_right _ _,
    prtOutDepOnly := rcn.prtOutDepOnly,
    actOutDepOnly := rcn.actOutDepOnly,
    normNoChild := rcn.normNoChild
  }

noncomputable def updateOutDeps {rcn : Reaction ι υ} {is : Finset ι} 
  (hp : ∀ i {o} (v : υ), (o ∉ is) → (Change.port o v) ∉ rcn i) 
  (ha : ∀ i {o} t (v : υ), (o ∉ is) → (Change.action o t v) ∉ rcn i) 
  : Reaction ι υ := 
  let deps' := Function.update rcn.deps Role.out is
  {
    deps := deps',
    triggers := rcn.triggers ∩ (deps' Role.in), 
    children := rcn.children,
    body := rcn.body,
    tsSubInDeps := Finset.inter_subset_right _ _,
    prtOutDepOnly := λ i _ v h' => hp i v h',
    actOutDepOnly := λ i _ v h' => ha i v h',
    normNoChild := rcn.normNoChild
  } 

noncomputable def updateTriggers {rcn : Reaction ι υ} {is : Finset ι} (h : is ⊆ rcn.deps Role.in) : Reaction ι υ := {
  deps := rcn.deps,
  triggers := is, 
  children := rcn.children,
  body := rcn.body,
  tsSubInDeps := h,
  prtOutDepOnly := rcn.prtOutDepOnly,
  actOutDepOnly := rcn.actOutDepOnly,
  normNoChild := rcn.normNoChild
}

noncomputable def updateChildren {rcn : Reaction ι υ} (is : Finset ι) (h : rcn.isMut) : Reaction ι υ := {
  deps := rcn.deps,
  triggers := rcn.triggers, 
  children := is,
  body := rcn.body,
  tsSubInDeps := rcn.tsSubInDeps,
  prtOutDepOnly := rcn.prtOutDepOnly,
  actOutDepOnly := rcn.actOutDepOnly,
  normNoChild := by
    simp only [isMut, isNorm] at h
    intro h'
    contradiction
}
    
end Reaction