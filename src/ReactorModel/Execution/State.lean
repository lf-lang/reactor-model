import ReactorModel.Execution.Reactor

noncomputable section
open Classical Reactor 

namespace Execution

variable [Hierarchical α]

@[ext]
structure State (α) where
  rtr      : α 
  tag      : Time.Tag
  clock    : Time
  progress : Set ID
  events   : Component → ID ⇀ Time.Tag ⇉ Value 

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

def «at» (s : State α) (t : Time) : State α := 
  { s with clock := t }

def schedule (s : State α) (cpt : Component) (i : ID) (t : Time) (v : Value) : State α := 
  { s with events := sorry } --  s.events.update cpt (·.update i (go · t v)) }
where 
  go (a : Time.Tag ⇉ Value) (t : Time) (v : Value) : Time.Tag ⇉ Value :=
    match a.keys.filter (·.time = t) |>.max with
    | ⊥           => a.insert ⟨t, 0⟩ v
    | some ⟨_, m⟩ => a.insert ⟨t, m + 1⟩ v

def scheduledTags (s : State α) : Set Time.Tag := 
  { g | ∃ cpt i a, (s.events cpt i = some a) ∧ (g ∈ a.keys) }

def logicals (s : State α) (g : Time.Tag) : ID ⇀ Value := 
  s.rtr[.log].mapIdx fun i => s.events .log i >>= (· g) |>.getD .absent

def physicals (s : State α) (g : Time.Tag) : ID ⇀ Value := 
  s.rtr[.phy].mapIdx fun i => s.events .phy i >>= (· g) |>.getD .absent

def unprocessed (s : State α) : Set ID :=
  { i ∈ s.rtr[.rcn] | i ∉ s.progress }

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

structure Terminal (s : State α) : Prop where
  closed  : s.Closed
  no_next : ∀ g, ¬s.NextTag g

protected structure Over (over : α) extends State α where 
  rtr_eq         : rtr = over := by rfl
  progress_sub   : progress ⊆ rtr[.rcn].ids 
  log_events_sub : (events .log).ids ⊆ rtr[.log].ids
  phy_events_sub : (events .phy).ids ⊆ rtr[.phy].ids

instance {rtr : α} : CoeOut (State.Over rtr) (State α) where
  coe := State.Over.toState

end Execution.State