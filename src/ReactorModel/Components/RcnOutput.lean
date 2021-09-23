import ReactorModel.Components.Reactor

variable (ι υ) [ID ι] [Value υ]

structure RcnOutput where
  prtVals : Ports ι υ
  state   : StateVars ι υ
  newCns  : List (ι × ι)
  delCns  : List (ι × ι)
  newRtrs : List (Reactor ι υ)
  delRtrs : List ι


