import digraph
import network.basic
import network.precedence
import network.ids
import network.algorithms
import set_theory.ordinal

namespace network

  noncomputable def propagate_edge (η : network.graph) (e : graph.edge) : network.graph := 
    η.update_input e.dst (η.output e.src)

  lemma propagate_edge_equiv (η : network.graph) (e : graph.edge) :
    propagate_edge η e ≈ η :=
    begin
      unfold propagate_edge,
      apply graph.update_input_equiv
    end

  private noncomputable def propagate_edges : network.graph → list graph.edge → network.graph
    | η [] := η
    | η (eₕ :: eₜ) := propagate_edges (propagate_edge η eₕ) eₜ

  lemma propagate_edges_equiv (η : network.graph) (e : list network.graph.edge) :
    propagate_edges η e ≈ η :=
    begin
      induction e generalizing η,
        {
          simp only [(≈)],
          finish 
        },
        {
          unfold propagate_edges,
          have h, from propagate_edge_equiv η e_hd,
          have h', from e_ih (propagate_edge η e_hd),
          exact trans_of (≈) h' h
        } 
    end

    open classical

  -- For all edges `e` with `e.src = p`, set `e.dst` to `v`.  
  private noncomputable def propagate_port (η : network.graph) (p : port.id) : network.graph := 
    propagate_edges η ((η.edges_out_of p).sort well_ordering_rel) 

  -- For all edges `e` with `e.src ∈ p`, set `e.dst` to `rtr.output.nth e.src`.  
  private noncomputable def propagate_ports : network.graph → list port.id → network.graph
    | η [] := η 
    | η (pₕ :: pₜ) := propagate_ports (propagate_port η pₕ) pₜ

  private noncomputable def propagate_output (η : network.graph) (i : reaction.id) : network.graph :=
    propagate_ports η ((η.rcn i).dₒ.sort well_ordering_rel)

  private noncomputable def run_reaction (η : network.graph) (i : reaction.id) : network.graph :=
    propagate_output (η.update_reactor i.rtr ((η.rtr i.rtr).run i.rcn) (reactor.run_equiv _ _)) i
      
  private noncomputable def run_topo : network.graph → list reaction.id → network.graph
    | η [] := η
    | η (topoₕ :: topoₜ) := run_topo (run_reaction η topoₕ) topoₜ

  theorem run_topo_equiv_net_graph (η : network.graph) (topo : list reaction.id) :
    η ≈ (run_topo η topo) :=
    begin
      sorry
    end

  lemma run_topo_unique_ports_inv (n : network) (topo : list reaction.id) : 
    (run_topo n.η topo).has_unique_port_ins :=
    begin
      have h, from run_topo_equiv_net_graph n.η topo,
      exact network.graph.edges_inv_unique_port_ins_inv h.left n.unique_ins
    end 
    
  lemma run_topo_prec_acyc_inv (n : network) (topo : list reaction.id) : 
    (run_topo n.η topo).is_prec_acyclic :=
    begin
      have h, from run_topo_equiv_net_graph n.η topo,
      exact network.graph.equiv_prec_acyc_inv h n.prec_acyclic
    end 

  noncomputable def run (n : network) (prec_func : prec_func) (topo_func : topo_func) : network :=
    let topo := topo_func (prec_func n) in
    let η' := run_topo n.η topo in
    {network . η := η', unique_ins := run_topo_unique_ports_inv n topo, prec_acyclic := run_topo_prec_acyc_inv n topo}

  theorem run_topo_indep (η : network.graph) (ρ : precedence.graph) (h_a : ρ.is_acyclic) (h_w : ρ.is_well_formed_over η) :
    ∃! output, ∀ (topo : list reaction.id) (_ : ρ.topological_order h_a topo), run_topo η topo = output :=
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

  /-lemma prop_edge_comm (σ : network) : 
    right_commutative (propagate_edge σ) :=
    begin
      unfold right_commutative,
      intros n e e',
      by_cases (e : graph.edge) = ↑e',
        rw (subtype.eq h),
        {
          have hₑ  : ↑e  ∈ (n : network), from edge_mem_equiv_trans n.property e.property,
          have hₑ' : ↑e' ∈ (n : network), from edge_mem_equiv_trans n.property e'.property,
          have hᵤ, from (n : network).unique_ins,
          rw graph.has_unique_port_ins at hᵤ,
          replace h : ↑e ≠ ↑e' := by exact h,
          have h_d : (e : graph.edge).dst ≠ (e' : graph.edge).dst, from hᵤ _ _ hₑ hₑ' h,
          unfold propagate_edge,
          simp,
          exact update_input_comm h_d _ _ ↑n
        }
    end-/

  /-lemma prop_port_comm : right_commutative propagate_port :=
    begin
      unfold right_commutative,
      intros n p p',
      unfold propagate_port,
      sorry
    end-/

end network