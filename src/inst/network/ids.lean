import inst.reactor

-- A type of unique identifiers for reactors in a network.
@[derive has_lt]
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
@[ext]
protected structure port.id := 
  (rtr : reactor.id)
  (prt : ℕ)

namespace port.id

  -- A (lexicographic) < for port-IDs.
  def lt : port.id → port.id → Prop := λ a b, 
    a.rtr < b.rtr ∨ (a.rtr = b.rtr ∧ a.prt < b.prt)

  instance has_lt : has_lt port.id := ⟨port.id.lt⟩

  -- Port-IDs' equality is non-constructively decidable.
  noncomputable instance dec_eq : decidable_eq port.id := classical.dec_eq _

end port.id

