import data.set
import basic
import action

structure reactor {reaction mutation contained_reactor: Type*} :=
  (inputs:             set identifier)
  (outputs:            set identifier)
  (actions:            set action)
  (state_vars:         set identifier)
  (reactions:          set reaction)
  (mutations:          set mutation)
  (contained_reactors: set contained_reactor)
  -- ...
