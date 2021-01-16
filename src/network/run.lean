import digraph
import network.basic
import network.precedence
import network.ids
import network.algorithms

namespace network

  noncomputable def propagate_edge (n : network) (e : network.graph.edge) : network :=
    n.update_input e.dst (n.η.output e.src)

  lemma r_comm_prop_edge : 
    right_commutative propagate_edge :=
    begin
      unfold right_commutative,
      intros n e e',
      unfold propagate_edge,
      -- Prove that e.dst must be ≠ e'.dst
    end

  noncomputable def propagate_port (n : network) (p : port.id) : network :=
    (n.η.edges_out_of p).val.foldl propagate_edge r_comm_prop_edge n 

  lemma r_comm_prop_port : right_commutative propagate_port :=
    sorry

  private noncomputable def propagate_ports (n : network) (p : finset port.id) : network :=
    p.val.foldl propagate_port r_comm_prop_port n 

  private noncomputable def propagate_output (n : network) (i : reaction.id) : network :=
    propagate_ports n ((n.η.rcn i).dₒ.image (λ d, {port.id . rtr := i.rtr, prt := d}))

  private noncomputable def run_reaction (n : network) (i : reaction.id) : network :=
    propagate_output (n.update_reactor i.rtr ((n.η.rtr i.rtr).run i.rcn) (reactor.run_equiv _ _)) i
      
  private noncomputable def run_topo : network → list reaction.id → network
    | n [] := n
    | n (topoₕ :: topoₜ) := run_topo (run_reaction n topoₕ) topoₜ

  -- Why do we choose to define a specific run-func instead of describing propositionally, what the
  -- output of such a function should look like?
  -- Because in this case it's easier to define the function, than it's properties.
  noncomputable def run (n : network) (prec_func : prec_func) (topo_func : topo_func) : network :=
    run_topo n (topo_func (prec_func n))

  theorem run_topo_indep (n : network) (ρ : precedence.graph) (h_a : ρ.is_acyclic) (h_w : ρ.is_well_formed_over n.η) :
    ∃! output, ∀ (topo : list reaction.id) (_ : ρ.topological_order h_a topo), run_topo n topo = output :=
    sorry

  theorem determinism (n : network) (p p' : prec_func) (t t' : topo_func) :
    n.run p t = n.run p' t' := 
    begin
      rw all_prec_funcs_are_eq p p',
      sorry
      -- Showing that the specific `topo_func` doesn't matter, will be tied to `run` itself.
      -- I.e. it's a quirk of `run` that the specific `topo_func` doesn't matter.
      -- This fact is captured by the theorem `run_topo_indep`.
    end

end network