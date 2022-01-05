import ReactorModel.Time
import ReactorModel.Components

structure State (ι υ) [Value υ] where
  time : Time.Tag
  execRcns : Finset ι