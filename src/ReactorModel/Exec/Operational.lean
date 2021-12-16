-- This file defines an operational semantics for 
-- the execution of reactors.
import ReactorModel.Components
import ReactorModel.Exec.State


-- The idea behind execution is the following:
-- We have different types of execution steps:
--  * instantaneousStep (no time-change)
import ReactorModel.Exec.Inst
--  * timedStep (changing the time of the model)
import ReactorModel.Exec.Timed
--  * executeStep (either of the two)

open Reactor Ports Classical State Inst Timed

-- We define ι and υ as variables to be added implicitly where we use them
variable {ι υ} [Value υ]

-- We define an execution step inductively as any of the two
-- possibilities above
inductive executeStep (r : Reactor ι υ) (s s' : State ι υ) : Prop
 | execInstantaneousStep (H : [s ⇓ᵢ s']r) : executeStep r s s'
 | execTimedStep (H : [s ⇓ₜ s']r) : executeStep r s s'

-- We add a notation to define an execution step accordingly
notation "[" s " ⇓ " s' "]" r:max => executeStep r s s'

-- An execution of a reactor model is a series of execution steps.
-- We model this with a reflexive transitive closure:
inductive execution (r : Reactor ι υ) : State ι υ → State ι υ → Prop
 | execRefl (s) : execution r s s
 | execStep {s sₘ s'} : [s ⇓ sₘ]r → execution r sₘ s' → execution r s s'

-- Again, we define a special notation for this closure 
-- (using the * operator)
notation "[" s " ⇓* " s' "]" r:max => execution r s s'