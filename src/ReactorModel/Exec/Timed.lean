-- This file defines the timed execution of reactors,
-- i.e. the aspects of the execution of reactors where time
-- is involved.
import ReactorModel.Exec.State

namespace Timed

variable {ι υ} [Value υ]

inductive timedStep (r : Reactor ι υ) (s s' : State ι υ) : Prop
 | changeMe 

notation "[" s " ⇓ₜ " s' "]" r:max => timedStep r s s'

end Timed