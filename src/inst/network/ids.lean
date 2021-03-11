import inst.reactor

-- A type of unique identifiers for reactors in a network.
@[derive has_le]
protected def reactor.id := ℕ

-- A type of unique identifiers for reactions in a network.
@[ext]
protected structure reaction.id := 
  (rtr : reactor.id) 
  (rcn : ℕ)
 
-- Reaction-IDs' equality is non-constructively decidable.
noncomputable instance : decidable_eq reaction.id := classical.dec_eq _

-- The type of unique identifiers for ports in a network.
@[ext]
protected structure port.id := 
  (rtr : reactor.id)
  (prt : ℕ)

-- Port-IDs' equality is non-constructively decidable.
noncomputable instance : decidable_eq port.id := classical.dec_eq _

-- We define a total order on port-IDs, as this is needed for `timed.network.action_edge_ge`.
instance : has_le port.id := ⟨λ p p', p.rtr ≤ p'.rtr ∨ (p.rtr = p'.rtr ∧ p.prt ≤ p'.prt)⟩
