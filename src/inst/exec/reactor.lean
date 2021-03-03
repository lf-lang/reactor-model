import inst.network.graph
import inst.prec.basic
import inst.prec.lemmas
import inst.exec.propagation.output

open network

variables {υ : Type*} [decidable_eq υ]

-- `rp.2` indicates which output ports should be propagated
noncomputable def apply_reactor (η : network.graph υ) (i : reactor.id) (rtr : reactor υ) : network.graph υ :=
  propagate_output (η.update_reactor i rtr) i ((η.rtr i).output.ne_indexes rtr.output).val.to_list

lemma apply_reactor_equiv (η : network.graph υ) (i : reactor.id) (rtr : reactor υ) (h : η.rtr i ≈ rtr) :
  apply_reactor η i rtr ≈ η :=
  begin
    unfold apply_reactor,
    apply propagate_output_equiv,
    apply graph.update_reactor_equiv,
    exact h
  end