import network.graph
import run.propagation.ports

open network

variables {υ : Type*} [decidable_eq υ]

noncomputable def propagate_output (η : network.graph υ) (i : reactor.id) (p : list ℕ) : network.graph υ :=
  propagate_ports η (p.map (λ x, {rtr := i, prt := x}))
  
lemma propagate_output_equiv (η η' : network.graph υ) (i : reactor.id) (p : list ℕ) (h : η ≈ η') :
  propagate_output η i p ≈ η' :=
  begin
    unfold propagate_output,
    induction (p.map (λ x, {port.id . rtr := i, prt := x}))
      ; apply propagate_ports_equiv
      ; exact h
  end

lemma propagate_output_out_inv (η : network.graph υ) {i : reactor.id} {p : list ℕ} :
  ∀ o, (propagate_output η i p).output o = η.output o :=
  by apply propagate_ports_out_inv

lemma propagate_output_comm (η : network.graph υ) (i i' : reactor.id) (p p' : list ℕ) (hᵤ : η.has_unique_port_ins) :
  propagate_output (propagate_output η i p) i' p' = propagate_output (propagate_output η i' p') i p :=
  propagate_ports_comm' _ _ _ hᵤ

-- lemma propagate_output_run_indep {η : network.graph} {i : reactor.id} {ps : list ℕ} {i' : reaction.id} :
  -- ¬ precedence.externally_dependent i i' η → progpagate_output :=

/-lemma propagate_output_input_inv (η : network.graph) {ρ : precedence.graph} {i i' : reaction.id} {p : list ℕ} (hₛ : p.to_finset ⊆ (η.rcn i).dₒ) :
  ¬(i~ρ~>i') → i.rtr ≠ i'.rtr → reactor.ports.correspond_at (η.rcn i').dᵢ ((propagate_output η i.rtr p).rtr i'.rtr).input (η.rtr i'.rtr).input :=
  begin
    intros hₚ hₙ,
    unfold reactor.ports.correspond_at,
    intros x hₓ,
    unfold propagate_output propagate_ports,
    simp,
    unfold propagate_port propagate_edges,
    

  end-/
