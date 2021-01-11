import reactor

-- An ID for a reactor that lives in a network of `n` reactors.
-- This `n` will usually be a `network`'s `c`.
protected def reactor.id (n : ℕ) := fin n

variables {c : ℕ} (reactors : reactor.id c → reactor)

-- An ID for a reaction that is part of a `network.graph` `n`.
-- This `n` will usually be a `precedence.graph`'s `n`.
protected structure reaction.id := 
  (rtr : reactor.id c)
  (rcn : fin (reactors rtr).nᵣ)

noncomputable instance : decidable_eq (reaction.id reactors) := 
  classical.type_decidable_eq _

protected structure port.id (c : ℕ):= 
  (rtr : reactor.id c)
  (prt : ℕ)

noncomputable instance : decidable_eq (port.id c) := 
  classical.type_decidable_eq _

variable {reactors}

def port_depends_on_reaction (p : port.id c) (r : reaction.id reactors) : Prop :=
  -- The ∃ is used as a dependent ∧ here.
  ∃ h : p.rtr = r.rtr, p.prt ∈ ((reactors r.rtr).reactions r.rcn).dₒ 

def reaction_depends_on_port (r : reaction.id reactors) (p : port.id c) : Prop :=
  -- The ∃ is used as a dependent ∧ here.
  ∃ h : p.rtr = r.rtr, p.prt ∈ ((reactors r.rtr).reactions r.rcn).dᵢ 