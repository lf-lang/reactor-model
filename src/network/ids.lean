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

-- The `dim` here is like a keypath and will usually be `reactor.nₒ` or `reactor.nᵢ`.
protected structure port.id (dim : reactor → ℕ) := 
  (rtr : reactor.id c)
  (prt : fin (dim (reactors rtr)))

noncomputable instance {dim : reactor → ℕ} : decidable_eq (port.id reactors dim) := 
  classical.type_decidable_eq _

variable {reactors}

theorem same_rtr_same_dims {dim : reactor → ℕ} (p : port.id reactors dim) (r : reaction.id reactors) :
  p.rtr = r.rtr → (reactors p.rtr).dims = ((reactors r.rtr).reactions r.rcn).dims :=
  begin
    intro h,
    rw h,
    let rtr := reactors r.rtr,
    let rcn := rtr.reactions r.rcn,
    have hₘ : rcn ∈ rtr, from ⟨r.rcn, refl _⟩, -- ∈ means ∃ p, rtr.reactions p = rcn
    rw reactor.dims,
    apply symm (rtr.rcn_dims rcn hₘ)
  end

def port_depends_on_reaction (p : port.id reactors reactor.nₒ) (r : reaction.id reactors) : Prop :=
  -- The ∃ is used as a dependent ∧ here.
  ∃ h : p.rtr = r.rtr,
    -- The `let`s are nothing more than a type cast.
    let dim_eq := (prod.mk.inj (same_rtr_same_dims p r h)).right in 
    let port_index := (fin.cast dim_eq p.prt) in
    port_index ∈ ((reactors r.rtr).reactions r.rcn).dₒ 

def reaction_depends_on_port (r : reaction.id reactors) (p : port.id reactors reactor.nᵢ) : Prop :=
  -- The ∃ is used as a dependent ∧ here.
  ∃ h : p.rtr = r.rtr, 
    -- The `let`s are nothing more than a type cast.
    let dim_eq := (prod.mk.inj (same_rtr_same_dims p r h)).left in 
    let port_index := (fin.cast dim_eq p.prt) in
    port_index ∈ ((reactors r.rtr).reactions r.rcn).dᵢ 