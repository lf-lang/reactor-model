import ReactorModel.Objects.Change

open Classical

@[ext]
structure Reaction.Input where
  ports : ID ⇀ Value
  acts  : ID ⇀ Value
  state : ID ⇀ Value
  tag   : Time.Tag

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
structure Reaction where
  deps :          Kind → Set ID
  triggers :      Set ID
  prio :          Priority
  body :          Reaction.Input → List Change
  tsSubInDeps :   triggers ⊆ deps .in
  prtOutDepOnly : ∀ i v,   (o ∉ deps .out) → (.port o v) ∉ body i
  actOutDepOnly : ∀ i t v, (o ∉ deps .out) → (.action o t v) ∉ body i
  actNotPast :    (.action a t v) ∈ body i → i.tag.time ≤ t
  stateLocal :    (.state s v) ∈ body i → s ∈ i.state.ids
  
namespace Reaction

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
  
-- The condition under which a given reaction triggers on a given (input) port-assignment.
def TriggersOn (rcn : Reaction) (i : Input) : Prop :=
  ∃ t v, (t ∈ rcn.triggers) ∧ (i.ports t = some v) ∧ (v.IsPresent)
  
-- Relay reactions are a specific kind of reaction that allow us to simplify what
-- it means for reactors' ports to be connected. We can formalize connections between
-- reactors' ports by creating a reaction that declares these ports and only these
-- ports as dependency and antidependency respectively, and does nothing but relay the
-- value from its input to its output.
def relay (src dst : ID) : Reaction where
  deps 
    | .in => {src} 
    | .out => {dst}
  triggers := {src}
  prio := none
  body i := 
    match i.ports src with 
    | none => [] 
    | some v => [.port dst v]
  tsSubInDeps := by simp
  prtOutDepOnly := by
    intro _ i 
    cases hs : i.ports src <;> simp_all [Option.elim, hs]
  actOutDepOnly := by
    intro _ i
    cases hs : i.ports src <;> simp [Option.elim, hs]
  actNotPast := by
    intro i _ _ _ h
    cases hs : i.ports src <;> simp [hs] at h
  stateLocal := by
    intro i _ _ h
    cases hs : i.ports src <;> simp [hs] at h

theorem Pure.relay (src dst) : Pure (relay src dst) where
  input := by intros; rw [relay]
  output := by 
    intro _ i h
    cases hc : i.ports src <;> (rw [relay] at h; simp [hc] at h)
    exact .inl $ h ▸ .intro

end Reaction