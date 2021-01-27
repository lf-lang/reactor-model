import missing
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

  instance : is_equiv reactor (≈) := 
    {
      symm := begin simp [(≈)], finish end,
      trans := begin simp [(≈)], finish end,
      refl := by simp [(≈)]
    }

  -- Two reactors are equal relative to a given reaction if they agree on everything, excluding
  -- their input-ports which only have to correspond relative to the given reaction.
  def eq_rel_to (rtr rtr' : reactor) (rcn_id : ℕ) : Prop :=
    rtr ≈ rtr' ∧ rtr.output = rtr'.output ∧ rtr.state = rtr'.state ∧ 
    ports.correspond_at (rtr.reactions rcn_id).dᵢ rtr.input rtr'.input

  noncomputable def priority_of (rtr : reactor) (rcn : reaction) (h : rcn ∈ rtr) : ℕ := 
    h.some

  noncomputable def run (rtr : reactor) (rcn_id : ℕ) : reactor × list ℕ :=
    if (rtr.reactions rcn_id).fires_on rtr.input then
      let os' := (rtr.reactions rcn_id) rtr.input rtr.state in
      ({output := rtr.output.merge os'.1, state := os'.2, ..rtr}, os'.1.inhabited_indices)
    else 
      (rtr, [])

  lemma run_equiv (rtr : reactor) (rcn_id : ℕ) : 
    rtr ≈ (rtr.run rcn_id).1 :=
    begin
      unfold run,
      by_cases (rtr.reactions rcn_id).fires_on rtr.input
        ; simp [h, (≈)]
    end

  lemma run_input_inv (rtr : reactor) (rcn_id : ℕ) :
    (rtr.run rcn_id).1.input = rtr.input :=
    begin
      unfold run,
      simp,
      by_cases hᵢ : (rtr.reactions rcn_id).fires_on rtr.input
        ; finish
    end

  lemma run_affected_ports_sub_dₒ (rtr : reactor) (rcn_id : ℕ) :
    (rtr.run rcn_id).2.to_finset ⊆ (rtr.reactions rcn_id).dₒ :=
    sorry

  theorem eq_rel_to_rcn_run (rtr rtr' : reactor) (rcn_id : ℕ) : 
    rtr.eq_rel_to rtr' rcn_id → (rtr.run rcn_id).1.eq_rel_to (rtr'.run rcn_id).1 rcn_id ∧ (rtr.run rcn_id).2 = (rtr'.run rcn_id).2 :=
    begin
      intro h,
      unfold eq_rel_to at h,
      simp [(≈)] at h,
      unfold run,
      simp,
      have h_f : (rtr.reactions rcn_id).fires_on rtr.input ↔ (rtr.reactions rcn_id).fires_on rtr'.input,
      from reaction.eq_fires_on_corr_input _ _ _ h.2.2.2,
      have h_w : (rtr.reactions rcn_id) rtr.input rtr'.state = (rtr.reactions rcn_id) rtr'.input rtr'.state,
      from (rtr.reactions rcn_id).well_behaved _ _ _ h.2.2.2,
      rw [h.2.2.1, ←h.1.1, h_w, h.1.2, h.2.1],
      by_cases hᵢ : (rtr'.reactions rcn_id).fires_on rtr.input,
        {
          rw if_pos hᵢ,
          rw ←h.1.2 at hᵢ ⊢,
          rw if_pos (h_f.mp hᵢ),
          simp,
          unfold eq_rel_to,
            repeat { split },
            exact h.2.2.2
        },
        {
          rw if_neg hᵢ,
          rw h.1.2 at h_f,
          rw if_neg ((not_iff_not_of_iff h_f).mp hᵢ),
          simp,
          unfold eq_rel_to,
          exact h
        }
    end

  def update_input (rtr : reactor) (i : ℕ) (v : option value) : reactor :=
    {input := rtr.input.update_nth i v, ..rtr}

  lemma update_input_equiv (rtr : reactor) (i : ℕ) (v : option value) : 
    rtr ≈ rtr.update_input i v :=
    begin
      unfold update_input,
      simp [(≈)]
    end

  lemma update_input_comm {i i' : ℕ} (h : i ≠ i') (v v' : option value) (rtr : reactor) :
    (rtr.update_input i v).update_input i' v' = (rtr.update_input i' v').update_input i v :=
    begin
      unfold update_input,
      simp,
      apply list.update_nth_comm _ _ _ _ _ h _,
    end

  lemma update_input_out_inv (rtr : reactor) (i : ℕ) (v : option value) :
    (rtr.update_input i v).output = rtr.output :=
    by unfold update_input

end reactor
