import ReactorModel.Components.Change

open Port Classical

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
  deps :          Port.Role → Finset ID
  triggers :      Finset ID
  prio :          Priority
  body :          Input → List Change
  tsSubInDeps :   triggers ⊆ deps Role.in
  prtOutDepOnly : ∀ i {o} (v : Value),     (o ∉ deps Role.out) → Change.port o v ∉ body i
  actOutDepOnly : ∀ i {o} (t) (v : Value), (o ∉ deps Role.out) → Change.action o t v ∉ body i
  actNotPast :    ∀ i a t (v : Value), (Change.action a t v) ∈ body i → i.time.t ≤ t
  
namespace Reaction

-- A coercion so that reactions can be called directly as functions.
-- So when you see something like `rcn p s` that's the same as `rcn.body p s`.
instance : CoeFun Reaction (λ _ => Input → List Change) where
  coe rcn := rcn.body

-- A reaction is normal ("norm") if its body produces no mutating changes.
def isNorm (rcn : Reaction) : Prop :=
  ∀ i c, (c ∈ rcn i) → ¬c.mutates 

-- A reaction is a mutation if it is not "normal", i.e. it does produce
-- mutating changes for some input.
def isMut (rcn : Reaction) : Prop := ¬rcn.isNorm

-- A reaction is pure if it does not interact with its parent reactor's state.
structure isPure (rcn : Reaction) : Prop where
  input : ∀ p a s₁ s₂ t, rcn ⟨p, a, s₁, t⟩ = rcn ⟨p, a, s₂, t⟩ 
  output : ∀ i c, c ∈ rcn.body i → ∃ p v, c = Change.port p v

theorem muts_not_pure (rcn : Reaction) : rcn.isMut → ¬rcn.isPure := by
  intro hm ⟨_, ho⟩
  simp [isMut, isNorm] at hm
  have ⟨i, c, hb, hm⟩ := hm
  have ho := ho i c hb
  cases c <;> (have ⟨_, _, _⟩ := ho; contradiction)
  
-- The condition under which a given reaction triggers on a given (input) port-assignment.
def triggersOn (rcn : Reaction) (i : Input) : Prop :=
  ∃ t, t ∈ rcn.triggers ∧ i.portVals.isPresent t
  
-- Relay reactions are a specific kind of reaction that allow us to simplify what
-- it means for reactors' ports to be connected. We can formalize connections between
-- reactors' ports by creating a reaction that declares these ports and only these
-- ports as dependency and antidependency respectively, and does nothing but relay the
-- value from its input to its output.
noncomputable def relay (src dst : ID) : Reaction := {
  deps := λ r => match r with | Role.in => Finset.singleton src | Role.out => Finset.singleton dst,
  triggers := Finset.singleton src,
  prio := none,
  body := λ i => match i.portVals[src] with | none => [] | some v => [Change.port dst v],
  tsSubInDeps := by simp,
  prtOutDepOnly := by
    intro i o v h hc
    cases hs : i.portVals[src] <;> simp [Option.elim, hs] at *
    case some v' =>
      rw [Finset.not_mem_singleton] at h
      exact absurd hc.left h
  actOutDepOnly := by
    intro i
    cases hs : i.portVals[src] <;> simp [Option.elim, hs]
  actNotPast := by
    intro i _ _ _ h
    cases hs : i.portVals[src] <;> (simp [hs] at h),
}

theorem relay_isPure (i₁ i₂ : ID) : (Reaction.relay i₁ i₂).isPure := by
  constructor 
  case input => simp [relay]
  case output =>
    intro i c h
    cases hc : i.portVals[i₁] <;> simp [relay, hc] at h
    exact ⟨_, _, h⟩
    
end Reaction