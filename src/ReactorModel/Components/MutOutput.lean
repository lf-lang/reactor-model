import ReactorModel.Components.Reactor

open Reactor

variable (ι υ) [ID ι] [Value υ]

structure MutOutput where
  prtVals : Ports ι υ
  state   : StateVars ι υ
  newCns  : List (ι × ι)
  delCns  : List (ι × ι)
  newRtrs : List (Reactor ι υ)
  delRtrs : Finset ι


