import data.set
import basic
import reaction
import priority

structure reactor :=
  (inputs:        set identifier)
  (outputs:       set identifier)
  (state_vars:    set identifier)
  (reactions:     set reaction)
  (priority_func: reaction → priority)
