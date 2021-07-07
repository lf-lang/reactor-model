import inst.reactor

-- A type of unique identifiers for reactors in a network.
@[derive linear_order]
protected def reactor.id := ℕ

-- A type of unique identifiers for reactions in a network.
@[ext]
protected structure reaction.id := 
  (rtr : reactor.id) 
  (rcn : ℕ)

-- Since reactions in a reactor are identified by their priorities, the `rcn` member of a `reaction.id` is the priority.
def reaction.id.priority (r : reaction.id) := r.rcn
 
-- Reaction-IDs' equality is non-constructively decidable.
noncomputable instance : decidable_eq reaction.id := classical.dec_eq _

-- The type of unique identifiers for ports in a network.
@[derive linear_order]
protected def port.id := lex reactor.id ℕ

namespace port.id

  -- Originally `port.id` was defined as a structure of `rtr` and `prt`.
  -- In order to easily derive `linear_order`, it is now a `lex`.
  -- So the following constructors and accessors replicate the original
  -- (structure-based) definition.
  @[simp] def mk (rtr : reactor.id) (prt : ℕ) : port.id := (rtr, prt)
  @[simp] def rtr (p : port.id) := p.1
  @[simp] def prt (p : port.id) := p.2

  -- Port-IDs' equality is non-constructively decidable.
  noncomputable instance dec_eq : decidable_eq port.id := classical.dec_eq _

end port.id

