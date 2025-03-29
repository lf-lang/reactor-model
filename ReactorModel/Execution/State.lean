import Mathlib.Data.Finset.Max
import ReactorModel.Execution.Reactor

noncomputable section
open Classical Reactor

namespace Execution

@[ext]
structure State (α) [Hierarchical α] where
  rtr      : α
  tag      : Time.Tag
  progress : Set (α✦)
  events   : α✦ ⇀ Time.Tag ⇉ α◾

variable [Hierarchical α]

namespace State

def input (s : State α) (rcn : α✦) : Reaction.Input α where
  val cpt := s.rtr[.rcn][rcn] |>.elim ∅ (restriction · cpt)
  tag := s.tag
where
  restriction (rcn : Reaction α) (cpt : Component.Valued) :=
    s.rtr[cpt].restrict { i | ⟨cpt, i⟩ ∈ rcn.deps .in }

def output (s : State α) (rcn : α✦) : Reaction.Output α :=
  s.rtr[.rcn][rcn] |>.elim [] (· <| s.input rcn)

def record (s : State α) (rcn : α✦) : State α :=
  { s with progress := s.progress.insert rcn }

def schedule (s : State α) (i : α✦) (t : Time) (v : α◾) : State α :=
  { s with events := s.events.update i (go · t v) }
where
  go (a : Time.Tag ⇉ α◾) (t : Time) (v : α◾) : Time.Tag ⇉ α◾ :=
    match a.keys.filter (·.time = t) |>.max with
    | ⊥           => a.insert ⟨t, 0⟩ v
    | some ⟨_, m⟩ => a.insert ⟨t, m + 1⟩ v

def scheduledTags (s : State α) : Set Time.Tag :=
  { g | ∃ i a, (s.events i = some a) ∧ (g ∈ a.keys) }

def actions (s : State α) (g : Time.Tag) : α✦ ⇀ α◾ :=
  s.rtr[.act].mapIdx fun i => s.events i >>= (· g) |>.getD ⊥

def unprocessed (s : State α) : Set α✦ :=
  { i ∈ s.rtr[.rcn] | i ∉ s.progress }

structure Allows (s : State α) (rcn : α✦) : Prop where
  mem         : rcn ∈ s.rtr[.rcn]
  deps        : dependencies s.rtr rcn ⊆ s.progress
  unprocessed : rcn ∉ s.progress

inductive Triggers (s : State α) (i : α✦) : Prop
  | intro (mem : s.rtr[.rcn][i] = some rcn) (triggers : rcn.TriggersOn (s.input i))

structure NextTag (s : State α) (next : Time.Tag) : Prop where
  mem   : next ∈ s.scheduledTags
  bound : s.tag < next
  least : ∀ g ∈ s.scheduledTags, (s.tag < g) → (next ≤ g)

def Closed (s : State α) : Prop :=
  s.progress = s.rtr[.rcn].ids

structure Terminal (s : State α) : Prop where
  closed  : s.Closed
  no_next : ∀ g, ¬s.NextTag g

protected structure Over (over : α) extends State α where
  rtr_eq       : rtr = over := by rfl
  progress_sub : progress ⊆ rtr[.rcn].ids
  events_sub   : events.ids ⊆ rtr[.act].ids

instance {rtr : α} : CoeOut (State.Over rtr) (State α) where
  coe := State.Over.toState

end Execution.State
