import ReactorModel.Objects.Change

open Classical

namespace Reaction

protected inductive Dependency
  | port (k : Kind) (i : ID)
  | action (i : ID)

@[ext]
structure Input where
  ports : Kind → ID ⇀ Value
  acts  : ID ⇀ Value
  state : ID ⇀ Value
  tag   : Time.Tag

def Input.value (i : Input) : Reaction.Dependency → Option Value
  | .port k j => i.ports k j
  | .action j => i.acts j

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
@[ext]
structure _root_.Reaction where
  deps :          Kind → Set Reaction.Dependency
  triggers :      Set Reaction.Dependency
  prio :          Priority
  body :          Input → List Change
  tsSubInDeps :   triggers ⊆ deps .in
  prtOutDepOnly : (.port k j v   ∈ body i) → .port k j ∈ deps .out 
  actOutDepOnly : (.action j t v ∈ body i) → .action j ∈ deps .out
  actNotPast :    (.action j t v ∈ body i) → i.tag.time ≤ t
  stateLocal :    (.state j v    ∈ body i) → j ∈ i.state.ids

-- A coercion so that reactions can be called directly as functions.
-- So when you see something like `rcn p s` that's the same as `rcn.body p s`.
instance : CoeFun Reaction (fun _ => Input → List Change) where
  coe rcn := rcn.body

-- A reaction is normal if its body only produces normal changes.
def Normal (rcn : Reaction) : Prop :=
  ∀ {i c}, (c ∈ rcn i) → c.IsNormal 

-- A reaction is a mutation if its body can produce mutating changes.
def Mutates (rcn : Reaction) : Prop := 
  ∃ i c, (c ∈ rcn i) ∧ c.IsMutation 

-- A reaction is pure if it does not interact with its container's state.
structure Pure (rcn : Reaction) : Prop where
  input : ∀ i s, rcn i = rcn { i with state := s }
  output : (c ∈ rcn.body i) → c.IsPort ∨ c.IsAction

theorem Mutates.not_Pure {rcn : Reaction} : rcn.Mutates → ¬rcn.Pure := by
  intro ⟨_, _, _, ⟨⟩⟩ ⟨_, ho⟩
  cases ho ‹_› <;> contradiction
  
-- The condition under which a given reaction triggers on a given input.
def TriggersOn (rcn : Reaction) (i : Input) : Prop :=
  ∃ t v, (t ∈ rcn.triggers) ∧ (i.value t = some v) ∧ (v.IsPresent)
  
-- Relay reactions are a specific kind of reaction that allow us to simplify what
-- it means for reactors' ports to be connected. We can formalize connections between
-- reactors' ports by creating a reaction that declares these ports and only these
-- ports as dependency and antidependency respectively, and does nothing but relay the
-- value from its input to its output.
def relay (src dst : ID) : Reaction where
  deps 
    | .in => {.port .out src} 
    | .out => {.port .in dst}
  triggers := {.port .out src}
  prio := none
  body i := 
    match i.ports .out src with 
    | none => [] 
    | some v => [.port .in dst v]
  tsSubInDeps   := by simp
  prtOutDepOnly := by intros; simp at *; split at * <;> simp_all 
  actOutDepOnly := by intros; simp at *; split at * <;> simp_all 
  actNotPast    := by intros; simp at *; split at * <;> simp_all 
  stateLocal    := by intros; simp at *; split at * <;> simp_all 

theorem Pure.relay (src dst) : Pure (relay src dst) where
  input := by intros; rw [relay]
  output := by 
    intro _ i h
    cases hc : i.ports .out src <;> (rw [relay] at h; simp [hc] at h)
    exact .inl $ h ▸ .intro

end Reaction