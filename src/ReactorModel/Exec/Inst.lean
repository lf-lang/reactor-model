-- This file defines the instantaneous execution of reactors.
-- This means that it does not deal with changes in time.
-- Instead, it explains how reactions and contained reactors
-- execute at a given time instant.

import ReactorModel.Exec.State
import ReactorModel.Components.Change
import ReactorModel.Time

open Change Time

namespace Inst

-- @Andrés: If happen to run into universe issues, try giving `ι` and `υ` the same universe level.
-- We define variables for ι and υ, to make them implicit arguments
-- when we use `Reactor`s.
variable {ι υ} [Value υ]

def applicationOfChange (c : Change ι υ) (σ₁ σ₂ : Reactor ι υ) : Prop :=
  match c with 
  | Change.port i v =>  σ₁ -[Cmp.prt, i:=v]→ σ₂ -- Port propagation isn't necessary/possible, because we're using relay reactions. 
  | Change.state i v => σ₁ -[Cmp.stv, i:=v]→ σ₂
  | Change.action i t v => ∃ a, σ₁.acts i = some a ∧ σ₁ -[Cmp.act, i := a.update t v]→ σ₂
  | _ => sorry

def applicationOfChangeList (l : List (Change ι υ)) (σ₁ σ₂ : Reactor ι υ) : Prop :=
  match l with
  | [] => σ₁ = σ₂
  | change::rest => ∃ σ₃, applicationOfChange change σ₁ σ₃ ∧ applicationOfChangeList rest σ₃ σ₂

-- An instantaneous step is basically the execution of a reaction
-- or a (nested) reactor. We want to model this as an inductively-defined
-- proposition. To do so, however, we first define functions to express
-- the expected behavior of reactions and reactors on state.

-- Executing a reaction yields a series of changes.
-- def executeChanges (s : State) (r : Reaction) :=

inductive instantaneousStep (r : Reactor ι υ) (s : State ι υ)
 (r' : Reactor ι υ) (s' : State ι υ) : Prop 
 | executeReaction (rcn : Reaction ι υ) (i : ι) (Hrcn : r.rcns i = rcn)
   (g : Time.Tag) (Htag : g = s.currentTime r)
   (HpreviousExectued : ∀ pred, pred ∈ r.predecessors i → pred ∈ s.executedRcns g)
   (HiNotExecuted : i ∉ s.executedRcnsVals g)
   (Hbody : applicationOfChangeList rcn.body σ₁ σ₂)
   (Htrigger : ∃ t ∈ rcn.triggers, r.ports.isPresent t)
   (HstateUpdated : sorry)
 | skipReaction (rcn : Reaction ι υ) (i : ι) (Hrcn : r.rcns i = rcn)
   (g : Time.Tag) (Htag : g = s.currentTime r)
   (HpreviousExectued : ∀ pred, pred ∈ r.predecessors i → pred ∈ s.executedRcns g)
   (HiNotExecuted : i ∉ s.executedRcns g)
   (HreactorUnchanged : r = r')
   (HnoTrigger : ∀ t ∈ rcn.triggers, ¬(r.ports.isPresent t))
   (HstateUpdated : sorry ) -- s 



-- We add a notation to write an instantaneous step.
notation "[" s " ⇓ᵢ " s' "]" r:max => instantaneousStep r s s'
-- | execPortChange (port i v : @Change ι υ) (Hss' : s'.ports  = s.ports.update i v)
-- | execChangeListHead ((c :: rest) : List (@Change ι υ)) (smid : @State ι υ)
--                  (Hhead : executeStep r s smid)
--
-- | execChangeListEmpty ([] : List (@Change ι υ)) (Hhead : executeStep r s smid)
--

end Inst