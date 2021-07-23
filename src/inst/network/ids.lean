import inst.reactor
open reactor

-- A type of unique identifiers for reactors in a network.
@[derive linear_order]
protected def reactor.id := ℕ

-- A type of unique identifiers for reactions in a network.
@[ext]
protected structure reaction.id := 
  (rtr : reactor.id) 
  (rcn : reactor.rcn_id)

-- Since reactions in a reactor are identified by their priorities, the `rcn` member of a `reaction.id` is the priority.
def reaction.id.priority (r : reaction.id) := r.rcn
 
-- The type of unique identifiers for ports in a network.
protected structure port.id (r : ports.role) :=
  (rtr : reactor.id)
  (prt : reaction.prt_id r)