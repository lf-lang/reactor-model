import ReactorModel.Execution.Reactor

noncomputable section
open Classical ReactorType 

namespace Execution

variable [Indexable α]

@[ext]
structure State (α) where
  rtr      : α 
  tag      : Time.Tag
  progress : Set ID
  events   : ID ⇀ Time.Tag ⇉ Value

namespace State

def input (s : State α) (rcn : ID) : Reaction.Input where
  val cpt := s.rtr[.rcn][rcn] |>.elim ∅ (restriction · cpt)
  tag := s.tag
where 
  restriction (rcn : Reaction) (cpt : Component.Valued) := 
    s.rtr[cpt].restrict { i | ⟨cpt, i⟩ ∈ rcn.deps .in }

def output (s : State α) (rcn : ID) : Reaction.Output := 
  s.rtr[.rcn][rcn] |>.elim [] (· $ s.input rcn)

def record (s : State α) (rcn : ID) : State α := 
  { s with progress := s.progress.insert rcn }

def schedule (s : State α) (i : ID) (t : Time) (v : Value) : State α := 
  { s with events := s.events.update i (go · t v) }
where 
  go (a : Time.Tag ⇉ Value) (t : Time) (v : Value) : Time.Tag ⇉ Value :=
    match a.keys.filter (·.time = t) |>.max with
    | ⊥           => a.insert ⟨t, 0⟩ v
    | some ⟨_, m⟩ => a.insert ⟨t, m + 1⟩ v

def scheduledTags (s : State α) : Set Time.Tag := 
  { g | ∃ i a, (s.events i = some a) ∧ (g ∈ a.keys) }

def actions (s : State α) (g : Time.Tag) : ID ⇀ Value := 
  fun i => s.events i >>= (· g)

structure Allows (s : State α) (rcn : ID) : Prop where
  mem         : rcn ∈ s.rtr[.rcn] 
  deps        : dependencies s.rtr rcn ⊆ s.progress
  unprocessed : rcn ∉ s.progress

inductive Triggers (s : State α) (i : ID) : Prop
  | intro (mem : s.rtr[.rcn][i] = some rcn) (triggers : rcn.TriggersOn (s.input i)) 

structure NextTag (s : State α) (next : Time.Tag) : Prop where
  mem   : next ∈ s.scheduledTags
  bound : s.tag < next
  least : ∀ g ∈ s.scheduledTags, (s.tag < g) → (next ≤ g)    

def Closed (s : State α) : Prop := 
  s.progress = s.rtr[.rcn].ids

def Nontrivial (s : State α) : Prop :=
  s.rtr[.rcn].Nonempty

end Execution.State