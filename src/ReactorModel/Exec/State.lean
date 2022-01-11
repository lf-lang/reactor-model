import ReactorModel.Time
import ReactorModel.Components
import ReactorModel.Mathlib.Finset

open Time Classical

variable {ι υ} [Value υ]

-- We model the state of the execution with 
-- a data structure, State, which records
-- which reactions have executed at which time.
-- this inclusdes reactions that have already been executed
-- (at an earlier time) or reactions that have not been executed
-- yet (at a later time)

structure State (ι υ) [Value υ] where
  executedRcns : Time.Tag ▸ Finset ι
  wellFormed : executedRcns.nonempty

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
def currentTime {s : State ι υ} (r : Reactor ι υ) : Time.Tag :=
  let nonexecutedTags := s.executedRcns.ids.filter (¬ s.tagExecuted r ·) 
  nonexecutedTags.min' sorry 
    -- WARNING: You can't remove this sorry because you can't prove that nonexecutedTags
    --          is nonempty, as State.wellFormed isn't strong enough of a condition.
    --          You also need to ensure that there is some reaction that r  hasn't executed yet.
    --          You could express this as a part of State.wellFormed, by making the State type dependent over a Reactor.

def executedRcnsVals (s : State ι υ) (g : Time.Tag) (HnotNone : s.executedRcns g ≠ none) : Finset ι :=
  let he := Option.ne_none_iff_exists.mp HnotNone
  let hs := Option.isSome_iff_exists.mpr ⟨he.choose, Eq.symm he.choose_spec⟩
  (s.executedRcns g).get hs

end State