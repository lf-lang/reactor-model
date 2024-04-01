import ReactorModel.Objects.Change

noncomputable section
open Classical

namespace Reaction 

protected structure Dependency where
  cpt : Component.Valued
  id  : ID

def _root_.Change.Normal.target (c : Change.Normal) : Reaction.Dependency where
  cpt := c.cpt
  id  := c.id

@[ext]
structure Input where
  val : Component.Valued → ID ⇀ Value
  tag : Time.Tag

abbrev Output := List Change

namespace Output

def targets (out : Output) :=
  { t : Component.Valued × ID | ∃ c ∈ out, c.Targets t.fst t.snd }

theorem mem_targets_cons (h : t ∈ targets tl) : t ∈ targets (hd :: tl) := by
  have ⟨c, hm, _⟩ := h 
  exists c, by simp [hm]

theorem target_mem_targets (hc : c ∈ out) (ht : c.target = some t) : t ∈ targets out := by
  exists c, hc
  cases c <;> simp [Change.target] at *
  subst ht
  constructor

end Output

-- Reactions are the components that can produce changes in a reactor system.
-- The can be classified into "normal" reactions and "mutations". The `Reaction`
-- type encompasses both of these flavors (cf. `isNorm` and `isMut`).
--
-- The `deps` field defines both dependencies and antidependencies by referring to
-- the ports' IDs and separating these IDs by the role of the port they refer to.
--
-- A reaction's `triggers` are a subset of its input ports (by `triggers_sub_in_deps`).
-- This field is used to define when a reaction triggers (cf. `triggersOn`).
--
-- The `outDepOnly` represents a constraint on the reaction's `body`.
@[ext]
structure _root_.Reaction where
  deps                 : Kind → Set Reaction.Dependency
  triggers             : Set Reaction.Dependency
  prio                 : Priority
  body                 : Input → Output
  triggers_sub_in_deps : triggers ⊆ { d | d ∈ deps .in ∧ d.cpt ≠ .stv } 
  target_mem_deps      : ∀ {c : Change.Normal}, (↑c ∈ body i) → c.target ∈ deps .out 

-- A coercion so that reactions can be called directly as functions.
-- So when you see something like `rcn p s` that's the same as `rcn.body p s`.
instance : CoeFun Reaction (fun _ => Input → Output) where
  coe rcn := rcn.body

-- A reaction is normal if its body only produces normal changes.
def Normal (rcn : Reaction) : Prop :=
  ∀ {i c}, (c ∈ rcn i) → c.IsNormal 

-- A reaction is a mutation if its body can produce mutating changes.
def Mutates (rcn : Reaction) : Prop := 
  ¬rcn.Normal

protected inductive Kind 
  | «mut»
  | norm

def kind (rcn : Reaction) : Reaction.Kind :=
  if rcn.Normal then .norm else .mut

-- The condition under which a given reaction triggers on a given input.
def TriggersOn (rcn : Reaction) (i : Input) : Prop :=
  ∃ t v, (t ∈ rcn.triggers) ∧ (i.val t.cpt t.id = some v) ∧ v.IsPresent

end Reaction