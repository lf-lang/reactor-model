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

  instance equiv : has_equiv reactor := ⟨λ r r', r.priorities = r'.priorities ∧ r.reactions = r'.reactions⟩

  instance : is_refl reactor (≈) := 
    ⟨by simp [(≈)]⟩

  def run (rtr : reactor) (rcn_id : ℕ) : reactor :=
    if (rtr.reactions rcn_id).fires_on rtr.input then
      let os' := (rtr.reactions rcn_id) rtr.input rtr.state in
      {output := os'.1, state := os'.2, ..rtr}
    else 
      rtr

  lemma run_equiv (rtr : reactor) (rcn_id : ℕ) : 
    rtr ≈ rtr.run rcn_id :=
    begin
      unfold run,
      by_cases (rtr.reactions rcn_id).fires_on rtr.input
        ; simp [h, (≈)]
    end

  def update_input (rtr : reactor) (i : ℕ) (v : option value) : reactor :=
    {input := rtr.input.update_nth i v, ..rtr}

  lemma update_input_equiv (rtr : reactor) (i : ℕ) (v : option value) : 
    rtr ≈ rtr.update_input i v :=
    begin
      unfold update_input,
      simp [(≈)]
    end

  noncomputable def priority_of (rtr : reactor) (rcn : reaction) (h : rcn ∈ rtr) : ℕ := 
    h.some

end reactor
