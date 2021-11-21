import ReactorModel.Components.Change

open Ports
open Classical

variable (ι υ) [ID ι] [Value υ]

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
  deps :        Ports.Role → Finset ι 
  triggers :    Finset ι
  children :    Finset ι
  body :        Ports ι υ → StateVars ι υ → List (Change ι υ)
  tsSubInDeps : triggers ⊆ deps Role.in
  outDepOnly :  ∀ p s {o} (v : υ), (o ∉ deps Role.out) → (Change.port o v) ∉ (body p s)
  normNoChild : (∀ i s c, c ∈ (body i s) → ¬c.mutates) → children = ∅

variable {ι υ}

namespace Reaction

-- A coercion so that reactions can be called directly as functions.
-- So when you see something like `rcn p s` that's the same as `rcn.body p s`.
instance : CoeFun (Reaction ι υ) (λ _ => Ports ι υ → StateVars ι υ → (List (Change ι υ))) where
  coe rcn := rcn.body

-- A reaction is normal ("norm") if its body produces no mutating changes.
def isNorm (rcn : Reaction ι υ) : Prop :=
  ∀ i s c, c ∈ (rcn i s) → ¬c.mutates

-- A reaction is a mutation if it is not "normal", i.e. it does produce
-- mutating changes for some input.
def isMut (rcn : Reaction ι υ) : Prop := ¬rcn.isNorm

-- A version of `Reaction.norm_no_child` that uses `isNorm`.
theorem norm_no_child' (rcn : Reaction ι υ) : rcn.isNorm → rcn.children = ∅ := 
  rcn.normNoChild

-- The condition under which a given reaction triggers on a given (input) port-assignment.
def triggersOn (rcn : Reaction ι υ) (p : Ports ι υ) : Prop :=
  ∃ t, t ∈ rcn.triggers ∧ p[t] ≠ none

-- TODO: Remove this if it is not used.
theorem eq_input_eq_triggering {rcn : Reaction ι υ} {p₁ p₂ : Ports ι υ} (h : p₁ =[rcn.deps Role.in] p₂) :
  rcn.triggersOn p₁ ↔ rcn.triggersOn p₂ := by
  simp [triggersOn, Ports.eqAt] at h ⊢
  apply Iff.intro <;> (
    intro ⟨t, ⟨hm, hn⟩⟩
    exists t
    exists hm
    have ht := h _ $ Finset.subset_iff.mp rcn.tsSubInDeps hm
    simp [ht] at hn ⊢
    assumption
  )
  
-- Relay reactions are a specific kind of reaction that allow us to simplify what
-- it means for reactors' ports to be connected. We can formalize connections between
-- reactors' ports by creating a reaction that declares these ports and only these
-- ports as dependency and antidependency respectively, and does nothing but relay the
-- value from its input to its output.
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
    
end Reaction