import reactor

protected def reactor.id := ℕ

protected structure reaction.id := 
  (rtr : ℕ) 
  (rcn : ℕ)

noncomputable instance : decidable_eq reaction.id := 
  classical.type_decidable_eq _

protected structure port.id := 
  (rtr : ℕ)
  (prt : ℕ)

noncomputable instance : decidable_eq port.id := 
  classical.type_decidable_eq _

instance port.id.has_le : has_le port.id := ⟨λ l r, if l.rtr = r.rtr then l.prt ≤ r.prt else l.rtr < r.rtr⟩
instance port.id.is_trans : is_trans port.id has_le.le := sorry
instance port.id.is_antisymm : is_antisymm port.id has_le.le := sorry
instance port.id.is_total : is_total port.id has_le.le := sorry