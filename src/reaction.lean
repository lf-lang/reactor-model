-- import data.set
import basic

structure reaction :=
  (dependencies:     set identifier)
  (triggers:         set identifier)
  (body:             code)
  (antidependencies: set identifier)