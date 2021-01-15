import digraph
import network.basic
import network.precedence
import network.ids
import network.algorithms

namespace network

  structure unapplied_net_graph :=
    (η : network.graph)
    (target : port.id)

  structure unapplied_edge_net_graph :=
    (η : network.graph)
    (edge : network.graph.edge)

  structure partially_applied_net_graph :=
    (η : network.graph)
    (changed : finset port.id)

  noncomputable instance : decidable_eq unapplied_edge_net_graph := classical.dec_eq _
  noncomputable instance : decidable_eq unapplied_net_graph := classical.dec_eq _

  private def merge (p p' : partially_applied_net_graph) : partially_applied_net_graph :=
    sorry

  instance : is_commutative partially_applied_net_graph merge := sorry
  instance : is_associative partially_applied_net_graph merge := sorry

  private noncomputable def single_apply (u : unapplied_edge_net_graph) : partially_applied_net_graph :=
    let v := u.η.output u.edge.src in
    let rtr := u.η.data u.edge.dst.rtr in
    let input' := rtr.input.update_nth u.edge.dst.prt v in
    let rtr' := {reactor . input := input', ..rtr} in
    let η' := u.η.update_data u.edge.dst.rtr rtr' in
    {η := η', changed := {u.edge.dst}}

  private noncomputable def partially_apply (u : unapplied_net_graph) : partially_applied_net_graph :=
    let e := (u.η.edges.filter (λ e, e.src = u.target)) in
    let u' := e.image (λ x, {unapplied_edge_net_graph . η := u.η, edge := x}) in
    {η := (finset.fold merge {partially_applied_net_graph . η := u.η, changed := ∅} single_apply u').η, changed := e.image graph.edge.dst} 

  -- For all edges `e` with `e.src ∈ p`, set `e.dst` to `rtr.output.nth e.src`.  
  private noncomputable def propagate_ports (η : network.graph) (u : finset unapplied_net_graph) : network.graph :=
    (finset.fold merge {partially_applied_net_graph . η := η, changed := ∅} partially_apply u).η

  private noncomputable def run_reaction (η : network.graph) (r_id : reaction.id) : network.graph :=
    let rtr := η.rtr r_id in
    let rcn := η.rcn r_id in
    if rcn.fires_on rtr.input then
      let ⟨p', s'⟩ := rcn rtr.input rtr.state in
      let rtr' := {reactor . output := p', state := s', ..rtr} in
      let η' : network.graph := η.update_data r_id.rtr rtr' in
      let affected_ports := rcn.dₒ.image (λ d, {port.id . rtr := r_id.rtr, prt := d}) in
      let u := affected_ports.image (λ p, {unapplied_net_graph . η := η', target := p}) in
      propagate_ports η' u
    else
      η
      
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

  -- Why do we choose to define a specific run-func instead of describing propositionally, what the
  -- output of such a function should look like?
  -- Because in this case it's easier to define the function, than it's properties.
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

end network