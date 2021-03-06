import inst.exec.propagation.output
open inst.network

variables {υ : Type*} [decidable_eq υ]

noncomputable def apply_reactor (η : graph υ) (i : reactor.id) (rtr : reactor υ) : graph υ :=
  propagate_output (η.update_reactor i rtr) i ((η.rtr i).output.index_diff rtr.output)

lemma apply_reactor_equiv (η : graph υ) (i : reactor.id) (rtr : reactor υ) (h : η.rtr i ≈ rtr) :
  apply_reactor η i rtr ≈ η :=
  begin
    unfold apply_reactor,
    apply propagate_output_equiv,
    apply graph.update_reactor_equiv,
    exact h
  end