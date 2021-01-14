import primitives
import reaction

open reactor
open reaction

-- It would be nice to declare reactors in a similar fashion to reactions.
-- I.e. reactions in themselves declare what they connect to (dᵢ and dₒ).
-- The difference is that reactions themselves are just a single "connection point",
-- so the mapping is a many-to-one (dependencies to reaction).
-- For reactors the mapping would have to be a many to many mapping (other reactors'
-- ports to own ports). This would on the one hand require the number of other reactors
-- to become part of a reactor's type, which seems inelegant. And further the mapping
-- would have to be implemented as a relation between another reactor's ports and the
-- self-reactor's ports. This would in turn also require nᵢ and nₒ to move into a 
-- reactor's type.

structure reactor :=
  (input : ports)
  (output : ports)
  (state : state_vars)
  (priorities : finset ℕ)
  (reactions : ℕ → reaction)

noncomputable instance : decidable_eq reactor := classical.dec_eq _

namespace reactor 

  @[reducible]
  instance mem : has_mem reaction reactor := {mem := λ rcn rtr, ∃ p ∈ rtr.priorities, rtr.reactions p = rcn}

  @[reducible]
  instance equiv : has_equiv reactor := ⟨λ r r', r.priorities = r'.priorities ∧ r.reactions = r'.reactions⟩

  lemma eq_imp_equiv {r r' : reactor} :
    r = r' → r ≈ r' :=
    by finish

  -- A list of a given reactor's reactions, ordered by their priority.
  def ordered_rcns (r : reactor) : list reaction :=
    (r.priorities.sort (≥)).map r.reactions

  -- A reaction is a member of a reactor's list of `ordered_reactions` iff it is also a member of
  -- the reactor itself.
  theorem ord_rcns_mem_rtr (rtr : reactor) :
    ∀ rcn : reaction, rcn ∈ rtr.ordered_rcns ↔ rcn ∈ rtr :=
    begin
      intro rcn,
      rw ordered_rcns,
      simp
    end

  noncomputable def priority_of (rtr : reactor) (rcn : reaction) (h : rcn ∈ rtr) : ℕ := 
    h.some

  private def run_aux (i : ports) (s : state_vars) (nₒ : ℕ) : list reaction → ports × state_vars
    | [] := (ports.empty nₒ, s)
    | (rₕ :: rsₜ) := let ⟨pₜ, sₜ⟩ := run_aux rsₜ in
      if rₕ.fires_on i 
      then let ⟨pₕ, sₕ⟩ := rₕ i sₜ in (pₜ.merge pₕ, sₕ)
      else (pₜ, sₜ)

  def run (r : reactor) : reactor := 
    let ⟨p, s⟩ := run_aux r.input r.state r.output.length r.ordered_rcns.reverse in
    {input := ports.empty r.input.length, output := p, state := s, ..r}

  theorem volatile_input (r : reactor) : 
    r.run.input.is_empty :=
    sorry

  theorem no_in_same_out (r : reactor) : 
    r.input.is_empty → r.run.output = r.output :=
    sorry

  theorem no_in_same_state (r : reactor) : 
    r.input.is_empty → r.run.state = r.state :=
    sorry

  theorem idempotence (r : reactor) :
    r.run = r.run.run :=
    sorry

  -- Running a single unconnected reactor on equal initial states leads to equal end states. 
  protected theorem determinism (r₁ r₂ : reactor) : 
    r₁ = r₂ → r₁.run = r₂.run :=
    assume h, h ▸ refl _

end reactor
