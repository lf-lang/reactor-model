import inst.reactor

-- A type of unique identifiers for reactors in a network.
protected def reactor.id := ℕ

-- A type of unique identifiers for reactions in a network.
@[ext]
protected structure reaction.id := 
  (rtr : reactor.id) 
  (rcn : ℕ)
 
-- Reaction-IDs' equality is non-constructively decidable.
noncomputable instance : decidable_eq reaction.id := classical.dec_eq _

-- The type of unique identifiers for ports in a network.
protected structure port.id := 
  (rtr : reactor.id)
  (prt : ℕ)

-- Port-IDs' equality is non-constructively decidable.
noncomputable instance : decidable_eq port.id := classical.dec_eq _