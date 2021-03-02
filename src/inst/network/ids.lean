import inst.reactor

protected def reactor.id := ℕ

@[ext]
protected structure reaction.id := 
  (rtr : reactor.id) 
  (rcn : ℕ)
 
noncomputable instance : decidable_eq reaction.id := 
  classical.type_decidable_eq _

protected structure port.id := 
  (rtr : reactor.id)
  (prt : ℕ)

noncomputable instance : decidable_eq port.id := 
  classical.type_decidable_eq _