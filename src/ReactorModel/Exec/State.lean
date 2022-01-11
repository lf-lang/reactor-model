import ReactorModel.Time
import ReactorModel.Components
import ReactorModel.Mathlib.Finset

open Time

variable {ι υ} [Value υ]

-- We model the state of the execution with 
-- a data structure, State, which records
-- which reactions have executed at which time.
-- this inclusdes reactions that have already been executed
-- (at an earlier time) or reactions that have not been executed
-- yet (at a later time)

structure State (ι υ) [Value υ] where
  executedRcns : Time.Tag ▸ Finset ι
  wellFormed : ∃ g, executedRcns g ≠ none

namespace State

-- to advance time we want to be able to add an (empty) finset
-- to a State at a new tag.
noncomputable def addTag (s: State ι υ) (g : Time.Tag) 
(Hempty : s.executedRcns g = none) : State ι υ := {
   executedRcns := s.executedRcns.update g (some ∅)
   wellFormed := sorry -- executedRcns.g = some ∅
}

-- A State can contain tags for which all reactions have been executed,
-- no reactions have been executed, or just some of them have.
-- We add a proposition stating that all reactions have been executed
-- at a particular tag.
noncomputable def tagExecuted (s : State ι υ) (r : Reactor ι υ) (g : Time.Tag) : Prop :=
  s.executedRcns g = some r.rcns.ids
  
-- We want to be able to refer to the current time
-- at which the execution of reactions is happening,
-- which is the least tag that has not been executed:
noncomputable def currentTime {s : State ι υ} (r : Reactor ι υ):=
  let tags := s.executedRcns.ids
  let unfinished_set := { g ∈ tags | ¬ (tagExecuted s r g) }
  let unfinished : Finset Time.Tag := { val := sorry, nodup := sorry} -- val should be unfinished_set as multiset
  unfinished.min'  

def executedRcnsVals (s : State ι υ) (g : Time.Tag) (HnotNone : s.executedRcns g ≠ none) :=
  (s.executedRcns g).iget  

end State