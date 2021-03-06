import inst.exec.propagation.ports
open reactor.ports
open inst.network

variables {υ : Type*} [decidable_eq υ]

noncomputable def propagate_output (η : graph υ) (i : reactor.id) (p : finset ℕ) : graph υ :=
  propagate_ports η (p.image (λ x, {rtr := i, prt := x}))
  
lemma propagate_output_equiv (η η' : graph υ) (i : reactor.id) (p : finset ℕ) (h : η ≈ η') :
  propagate_output η i p ≈ η' :=
  begin
    unfold propagate_output,
    induction (p.map (λ x, {port.id . rtr := i, prt := x}))
      ; apply propagate_ports_equiv
      ; exact h
  end

lemma propagate_output_out_inv (η : graph υ) {i : reactor.id} {p : finset ℕ} :
  ∀ o, (propagate_output η i p).port role.output o = η.port role.output o :=
  by apply propagate_ports_out_inv

lemma propagate_output_comm (η : graph υ) (i i' : reactor.id) (p p' : finset ℕ) (hᵤ : η.has_unique_port_ins) :
  propagate_output (propagate_output η i p) i' p' = propagate_output (propagate_output η i' p') i p :=
  propagate_ports_comm' _ _ _ hᵤ
