import reactor

protected def reactor.id := ℕ

protected structure reaction.id := 
  (rtr : ℕ) 
  (rcn : ℕ)

noncomputable instance : decidable_eq (reaction.id) := 
  classical.type_decidable_eq _

protected structure port.id := 
  (rtr : ℕ)
  (prt : ℕ)

noncomputable instance : decidable_eq (port.id) := 
  classical.type_decidable_eq _