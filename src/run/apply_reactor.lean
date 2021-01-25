import network.graph
import precedence.basic
import run.propagate_output

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
  begin
    intros o h,
    unfold apply_reactor,
    unfold graph.output,
  end

lemma apply_reactor_run_eq_rel_to (η : network.graph) (hᵤ : η.has_unique_port_ins) (ρ : precedence.graph) (h_wf : ρ.is_well_formed_over η) (i i' : reaction.id) (hᵢ : i ≠ i') :
  ¬(i~ρ~>i') → ¬(i'~ρ~>i) → reactor.eq_rel_to ((apply_reactor η i.rtr ((η.rtr i.rtr).run i.rcn)).rtr i'.rtr) (η.rtr i'.rtr) i'.rcn :=
  begin
    intros hₚ hₚ',    
    have hᵣ, from precedence.graph.indep_rcns_neq_rtrs h_wf hᵢ hₚ hₚ',
    unfold apply_reactor,
    sorry
  end