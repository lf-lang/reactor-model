import ReactorModel.Objects.Change

noncomputable section
open Classical Reactor

namespace Reaction 

protected structure Dependency where
  cpt : Component.Valued
  id  : ID

def _root_.Change.Normal.target (c : Change.Normal) : Reaction.Dependency where
  cpt := c.cpt
  id  := c.id

@[ext]
structure Input where
  val : (cpt : Component.Valued) → ID ⇀ cpt.type 
  tag : Time.Tag

inductive Input.IsPresent (i : Input) : (Reaction.Dependency) → Prop
  | prt : (i.val (.prt k) j = some (.present v))           → IsPresent i ⟨.prt k, j⟩  
  | stv : (i.val .stv j = some (.present v))               → IsPresent i ⟨.stv, j⟩ 
  | act : (i.val .act j >>= (· i.tag) = some (.present v)) → IsPresent i ⟨.act, j⟩ 

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
  deps      : Kind → Set Reaction.Dependency
  triggers  : Set Reaction.Dependency
  prio      : Priority
  body      : Input → List Change
  triggers_sub_in_deps : triggers ⊆ { d | d ∈ deps .in ∧ d.cpt ≠ .stv } 
  target_mem_deps      : ∀ {c : Change.Normal}, (↑c ∈ body i) → c.target ∈ deps .out 
  -- TODO: We don't need the following condictions for determinism. Should we remove them?
  act_not_past         : (.act j t v ∈ body i) → i.tag.time ≤ t
  act_local            : True -- `body` outputs the same even if we change all actions' past and future values.

-- A coercion so that reactions can be called directly as functions.
-- So when you see something like `rcn p s` that's the same as `rcn.body p s`.
instance : CoeFun Reaction (fun _ => Input → List Change) where
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
  ∃ t, (t ∈ rcn.triggers) ∧ (i.IsPresent t)

end Reaction