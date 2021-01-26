import network.graph
import precedence.basic
import precedence.lemmas
import run.propagation.output

open network

-- `rp.2` indicates which output ports should be propagated
noncomputable def apply_reactor (η : network.graph) (i : reactor.id) (rp : reactor × list ℕ) : network.graph :=
  propagate_output (η.update_reactor i rp.1) i rp.2

lemma apply_reactor_equiv (η : network.graph) (i : reactor.id) (rp : reactor × list ℕ) (h : η.rtr i ≈ rp.1) :
  apply_reactor η i rp ≈ η :=
  begin
    unfold apply_reactor,
    apply propagate_output_equiv,
    apply graph.update_reactor_equiv,
    exact h
  end

lemma apply_reactor_output_inv (η : network.graph) {i : reactor.id} {rp : reactor × list ℕ} :
  ∀ o : port.id, o.rtr ≠ i → (apply_reactor η i rp).output o = η.output o :=
  sorry

-- THIS IS FALSE
-- The second reactor needs to be able to depend on the first one, in the sense that the first one might change some of the second reactor's input ports.
-- Hence we get `apply_reactor_run_eq_rel_to` below.
lemma apply_reactor_comm_ (η : network.graph) (i i' : reactor.id) (rp rp' : reactor × list ℕ) (hᵤ : η.has_unique_port_ins) :
  apply_reactor (apply_reactor η i rp) i' rp' = apply_reactor (apply_reactor η i' rp') i rp :=
  sorry

lemma apply_reactor_comm {η : network.graph} {ρ : precedence.graph} (h : ρ.is_well_formed_over η) {i i' : reaction.id} :
  i ≠ i' → ¬(i~ρ~>i') → ¬(i'~ρ~>i) → true :=
  begin
    intros hₙ hₚ hₚ',
    have hₒ, from precedence.graph.indep_rcns_no_edge h hₙ hₚ hₚ',
    sorry
  end

-- lemma apply_reactor_indep {η : network.graph} (hᵤ : η.has_unique_port_ins) {ρ : precedence.graph} (h_wf : ρ.is_well_formed_over η) {i i' : reaction.id} (hᵢ : i ≠ i') {rp : reactor × list ℕ} (h_rp : rp.2.to_finset ⊆ (η.rcn i).dₒ) :
  -- ¬(i~ρ~>i') → ¬(i'~ρ~>i)

-- Say we have two independent reactions `i` and `i'`, a reactor (for the position `i.rtr`) and a
-- list of output ports of that reactor `rp.2` such that those ports are only part of `i`'s output
-- dependencies. 
-- Then applying that reactor, i.e. setting it and propagating its outputs, does not affect any of
-- `i'`'s dependencies (`dᵢ` ports).
lemma apply_reactor_run_eq_rel_to {η : network.graph} (hᵤ : η.has_unique_port_ins) {ρ : precedence.graph} (h_wf : ρ.is_well_formed_over η) {i i' : reaction.id} (hᵢ : i ≠ i') {rp : reactor × list ℕ} (h_rp : rp.2.to_finset ⊆ (η.rcn i).dₒ) :
  ¬(i~ρ~>i') → ¬(i'~ρ~>i) → reactor.eq_rel_to ((apply_reactor η i.rtr rp).rtr i'.rtr) (η.rtr i'.rtr) i'.rcn :=
  -- ¬(i~ρ~>i') → ¬(i'~ρ~>i) → reactor.eq_rel_to ((apply_reactor η i.rtr ((η.rtr i.rtr).run i.rcn)).rtr i'.rtr) (η.rtr i'.rtr) i'.rcn :=
  begin
    intros hₚ hₚ',    
    have hᵣ, from precedence.graph.indep_rcns_neq_rtrs h_wf hᵢ hₚ hₚ',
    unfold apply_reactor,
    sorry
  end