-- This file defines the instantaneous execution of reactors.
-- This means that it does not deal with changes in time.
-- Instead, it explains how reactions and contained reactors
-- execute at a given time instant.

import ReactorModel.Time
import ReactorModel.Components
import ReactorModel.Exec.State

open Reactor Ports Classical State

namespace Inst

-- @Andrés: If happen to run into universe issues, try giving `ι` and `υ` the same universe level.
-- We define variables for ι and υ, to make them implicit arguments
-- when we use `Reactor`s.
variable {ι υ} [Value υ]

-- An instantaneous step is basically the execution of a reaction
-- or a (nested) reactor. We want to model this as an inductively-defined
-- proposition. To do so, however, we first define functions to express
-- the expected behavior of reactions and reactors on state.

-- Executing a reaction yields a series of changes.
-- def executeChanges (s : State) (r : Reaction) :=
 
inductive instantaneousStep (r : Reactor ι υ) (s s' : State ι υ) : Prop 
 | changeMe

-- We add a notation to write an instantaneous step.
notation "[" s " ⇓ᵢ " s' "]" r:max => instantaneousStep r s s'
-- | execPortChange (port i v : @Change ι υ) (Hss' : s'.ports  = s.ports.update i v)
-- | execChangeListHead ((c :: rest) : List (@Change ι υ)) (smid : @State ι υ)
--                  (Hhead : executeStep r s smid)
--
-- | execChangeListEmpty ([] : List (@Change ι υ)) (Hhead : executeStep r s smid)
--

end Inst