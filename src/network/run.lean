import network.basic
import network.precedence
import graphs.dag

namespace network

  variable {c : ℕ}

  private def run_topo (n : network.graph c) (topo : list (precedence.graph.reaction_id n)) : (network.graph c) × list (precedence.graph.reaction_id n)
    := sorry

  -- Thinking:
  -- We have a network graph N.
  -- By the contraints of a network, 
  --  * we know that N has unique port inputs.
  --  * we know there must exist a precedence graph P for N that is well-formed and acyclic.
  -- 
  -- Proposition 1: The uniqueness of port inputs in N is independent of the port-values in N.
  -- Proposition 2: The existence of a well-formed, acyclic precedence graph for N is independent of N's port-values.
  -- Proposition 3: `run_topo` only changes port-values of N, nothing else.
  -- 
  -- (1) + (3): The resulting N of `run_topo` still has input-port-uniqueness.
  -- (2) + (3): There still exists a suitable prec-graph for the N resulting from `run_topo`.

  theorem run_topo_unique_ports_inv (n : network.graph c) (topo : list (precedence.graph.reaction_id n)) : 
    (run_topo n topo).1.has_unique_port_ins :=
    sorry

  theorem run_topo_prec_constr_inv (n : network.graph c) (topo : list (precedence.graph.reaction_id n)) : 
    precedence_constraints (run_topo n topo).1 :=
    sorry

  theorem run_topo_indep (n : network.graph c) (p : precedence.graph n) (h_a : p.is_acyclic) (h_w : p.is_well_formed) :
    ∃! output, ∀ (topo : list (precedence.graph.reaction_id n)) (h : dag.topological_order ⟨p, h_a⟩ topo), 
      run_topo n topo = output :=
    sorry

  noncomputable def run (n : network c) : network c :=
    let prec_graph := classical.subtype_of_exists n.constraints in
    let topo := (dag.any_dag_has_topo ⟨prec_graph.val, prec_graph.property.2⟩).some in
    let depiction' := (run_topo n.depiction topo).1 in
    {network . 
      depiction := depiction', 
      unique_ins := run_topo_unique_ports_inv n.depiction topo, 
      constraints := run_topo_prec_constr_inv n.depiction topo
    }

  -- Execution of the reactor network needs to be the same no matter which concrete topo-list it gets.
  --
  -- noncomputable def run (n : network) :=
  -- let p := n.prec in
  -- let topo := classical.choice theorem in
  --
  -- still need show that the result of running will still be the same no matter which topo we get.
  -- noncomputable func arent same-in-same-out
  --
  -- the core of the determinism-proof is the fact that run is the same no matter which topo order we get.

end network