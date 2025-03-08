import ReactorModel.Objects.Change

noncomputable section
open Classical

namespace Reaction

protected structure Dependency (ι) where
  cpt : Component.Valued
  id  : ι

def _root_.Change.Normal.target [Identifiable α] [Valued α] (c : Change.Normal α) :
    Reaction.Dependency α✦ where
  cpt := c.cpt
  id  := c.id

@[ext]
structure Input (α) [Identifiable α] [Valued α] where
  val : Component.Valued → α✦ ⇀ α◾
  tag : Time.Tag

abbrev Output (α) [Identifiable α] [Valued α] := List (Change α)

namespace Output

variable [Identifiable α] [Valued α]

def targets (out : Output α) :=
  { t : Component.Valued × α✦ | ∃ c ∈ out, c.Targets t.fst t.snd }

theorem mem_targets_cons {tl : Output α} (h : t ∈ targets tl) : t ∈ targets (hd :: tl) := by
  have ⟨c, hm, _⟩ := h
  exists c, by simp [hm]

theorem target_mem_targets {out : Output α} (hc : c ∈ out) (ht : c.target = some t) :
    t ∈ targets out := by
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
structure _root_.Reaction (α) [Identifiable α] [Valued α] where
  deps                 : Kind → Set (Reaction.Dependency α✦)
  triggers             : Set (Reaction.Dependency α✦)
  prio                 : Priority
  body                 : (Input α) → (Output α)
  triggers_sub_in_deps : triggers ⊆ { d | d ∈ deps .in ∧ d.cpt ≠ .stv }
  target_mem_deps      : ∀ {c : Change.Normal α}, (↑c ∈ body i) → c.target ∈ deps .out

variable [Identifiable α] [Valued α]

-- A coercion so that reactions can be called directly as functions.
-- So when you see something like `rcn p s` that's the same as `rcn.body p s`.
instance : CoeFun (Reaction α) (fun _ => Input α → Output α) where
  coe rcn := rcn.body

-- A reaction is normal if its body only produces normal changes.
def Normal (rcn : Reaction α) : Prop :=
  ∀ {i c}, (c ∈ rcn i) → c.IsNormal

-- A reaction is a mutation if its body can produce mutating changes.
def Mutates (rcn : Reaction α) : Prop :=
  ¬rcn.Normal

protected inductive Kind
  | «mut»
  | norm

def kind (rcn : Reaction α) : Reaction.Kind :=
  if rcn.Normal then .norm else .mut

-- The condition under which a given reaction triggers on a given input.
def TriggersOn (rcn : Reaction α) (i : Input α) : Prop :=
  ∃ t v, (t ∈ rcn.triggers) ∧ (i.val t.cpt t.id = some v) ∧ (v ≠ ⊥)

end Reaction
