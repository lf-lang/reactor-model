import network.graph
import precedence.basic
import run.reactor

open network

variables {υ : Type*} [decidable_eq υ]

noncomputable def run_reaction (η : network.graph υ) (i : reaction.id) : network.graph υ :=
  apply_reactor η i.rtr ((η.rtr i.rtr).run i.rcn)
    
lemma run_reaction_equiv (η : network.graph υ) (i : reaction.id) :
  run_reaction η i ≈ η :=
  begin
    unfold run_reaction,
    apply apply_reactor_equiv,
    apply reactor.run_equiv
  end

lemma run_reaction_output_inv (η : network.graph υ) {i : reaction.id} :
  ∀ r, i.rtr ≠ r → ((run_reaction η i).rtr r).output = (η.rtr r).output :=
  begin
    intros r h,
    unfold run_reaction,
    -- rw apply_reactor_output_inv _ h,
    sorry
  end

lemma run_reaction_state_inv (η : network.graph υ) {i : reaction.id} :
  ∀ r, i.rtr ≠ r → ((run_reaction η i).rtr r).state = (η.rtr r).state :=
  begin
    sorry
  end

lemma run_reaction_indep_eq {η : network.graph υ} (hᵤ : η.has_unique_port_ins) {ρ : precedence.graph υ} (h_wf : ρ.is_well_formed_over η) {i i' : reaction.id} :
  ¬(i~ρ~>i') → i.rtr ≠ i'.rtr → ((run_reaction η i).rtr i'.rtr).eq_rel_to (η.rtr i'.rtr) i'.rcn :=
  begin
    intros hₚ hₙ,
    unfold reactor.eq_rel_to,
    split,
      {
        have h, from run_reaction_equiv η i,
        simp [(≈)] at h,
        exact h.2.2 i'.rtr
      },
      repeat { split },
        exact run_reaction_output_inv _ _ hₙ,
        exact run_reaction_state_inv _ _ hₙ,
        sorry
  end

-- If there is no path between two reactions in a precedence graph, then they are independent,
-- i.e. their order of execution doesn't matter.
lemma run_reaction_comm {η : network.graph υ} (hᵤ : η.has_unique_port_ins) {ρ : precedence.graph υ} (h_wf : ρ.is_well_formed_over η) {i i' : reaction.id} :
  ¬(i~ρ~>i') → ¬(i'~ρ~>i) → run_reaction (run_reaction η i) i' = run_reaction (run_reaction η i') i :=
  begin 
    intros hₚ hₚ',
    by_cases hᵢ : i = i',
      rw hᵢ,
      {
        have h_ir, from precedence.graph.indep_rcns_neq_rtrs h_wf hᵢ hₚ hₚ',
        have h_ert  : ((run_reaction η i).rtr i'.rtr).eq_rel_to (η.rtr i'.rtr) i'.rcn, from run_reaction_indep_eq hᵤ h_wf hₚ h_ir,
        have h_ert' : ((run_reaction η i').rtr i.rtr).eq_rel_to (η.rtr i.rtr) i.rcn, from run_reaction_indep_eq hᵤ h_wf hₚ' (ne.symm h_ir),
        -- have hₛ : reactor.eq_rel_to ((apply_reactor η i.rtr ((η.rtr i.rtr).run i.rcn)).rtr i'.rtr) (η.rtr i'.rtr) i'.rcn,
        -- from apply_reactor_run_eq_rel_to _ hᵤ _ h_wf _ _ hᵢ hₚ hₚ',
        -- have hₛ' : reactor.eq_rel_to ((apply_reactor η i'.rtr ((η.rtr i'.rtr).run i'.rcn)).rtr i.rtr) (η.rtr i.rtr) i.rcn,
        -- from apply_reactor_run_eq_rel_to _ hᵤ _ h_wf _ _ (ne.symm hᵢ) hₚ' hₚ,
        -- have hᵣ, from reactor.eq_rel_to_rcn_run _ _ _ hₛ,
        -- have hᵣ', from reactor.eq_rel_to_rcn_run _ _ _ hₛ',

        -- simp [hₛ, hₛ'],
        -- rw apply_reactor_comm _ _ _ _ _ hᵣ hᵤ sorry sorry sorry sorry,
        sorry
      }
  end