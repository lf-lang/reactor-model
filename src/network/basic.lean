import network.graph
import network.precedence

open network

structure network :=
  (η : network.graph)
  (unique_ins : η.has_unique_port_ins)
  (prec_acyclic : η.is_prec_acyclic) -- In the long term this should be temporary.

namespace network

  noncomputable def update_reactor (n : network) (i : reactor.id) (r : reactor) (h : n.η.data i ≈ r) : network :=
    {
      η := n.η.update_data i r,
      unique_ins := graph.edges_inv_unique_port_ins_inv (refl _) n.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.update_with_equiv_rtr_is_equiv _ _ _ h) n.prec_acyclic
    }

  noncomputable def update_input (n : network) (p : port.id) (v : option value) : network :=
    update_reactor n p.rtr ((n.η.data p.rtr).update_input p.prt v) (reactor.update_input_equiv _ _ _)

end network