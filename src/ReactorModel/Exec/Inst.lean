import ReactorModel.Time
import ReactorModel.Components
import ReactorModel.State

open Reactor Ports Classical State

namespace Inst

-- @Andrés: If happen to run into universe issues, try giving `ι` and `υ` the same universe level.
variable {ι υ} [Value υ]


inductive executeStep (r : Reactor ι υ) (s : @State ι υ) (s' : @State ι υ) : Prop 
 | execPortChange (port i v : @Change ι υ) (Hss' : s'.ports  = s.ports.update i v)
 --| exec




end Inst