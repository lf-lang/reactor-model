import digraph
import network.basic
import network.precedence
import network.ids
import network.algorithms

namespace network

  instance port.id.has_le : has_le port.id := ⟨λ l r, if l.rtr = r.rtr then l.prt ≤ r.prt else l.rtr < r.rtr⟩
  instance port.id.is_trans : is_trans port.id has_le.le := sorry
  instance port.id.is_antisymm : is_antisymm port.id has_le.le := sorry
  instance port.id.is_total : is_total port.id has_le.le := sorry
  instance graph.edge.has_le : has_le graph.edge := ⟨λ l r, if l.src = r.src then l.dst ≤ r.dst else l.dst ≤ r.dst⟩
  instance graph.edge.is_trans : is_trans graph.edge has_le.le := sorry
  instance graph.edge.is_antisymm : is_antisymm graph.edge has_le.le := sorry
  instance graph.edge.is_total : is_total graph.edge has_le.le := sorry

  private noncomputable def propagate_edges (v : value) : network.graph → list network.graph.edge → network.graph
    | η [] := η
    | η (eₕ :: eₜ) :=
      let rtr := (η.data eₕ.dst.rtr) in
      let input' := rtr.input.update_nth eₕ.dst.prt v in
      let rtr' := {reactor . input := input', ..rtr} in
      let η' := η.update_data eₕ.dst.rtr rtr' in
      propagate_edges η' eₜ

  lemma propagate_edges_equiv_net_graph (η : network.graph) (e : list network.graph.edge) (v : value) :
    η ≈ (propagate_edges v η e) :=
    begin
      induction e,
        {
          simp only [(≈)],
          finish
        },
        {
          unfold propagate_edges,
          simp only [(≈)],
          sorry
        }
    end

  -- For all edges `e` with `e.src = p`, set `e.dst` to `v`.  
  private noncomputable def propagate_port (η : network.graph) (p : port.id) (v : value) : network.graph := 
    let affected_edges := η.edges.filter (λ e, e.src = p) in
    propagate_edges v η (affected_edges.sort (≤))

  -- For all edges `e` with `e.src ∈ p`, set `e.dst` to `rtr.output.nth e.src`.  
  private noncomputable def propagate_ports : network.graph → list port.id → network.graph
    | η [] := η 
    | η (pₕ :: pₜ) :=
      let v := η.output pₕ in
      let η' := v.elim η (λ v', propagate_port η pₕ v') in
      propagate_ports η' pₜ

  private noncomputable def run_reaction (η : network.graph) (r_id : reaction.id) : network.graph :=
    let rtr := η.rtr r_id in
    let rcn := η.rcn r_id in
    if rcn.fires_on rtr.input then
      let ⟨p', s'⟩ := rcn rtr.input rtr.state in
      let rtr' := {reactor . output := p', state := s', ..rtr} in
      let η' := η.update_data r_id.rtr rtr' in
      let affected_ports := rcn.dₒ.image (λ d, {port.id . rtr := r_id.rtr, prt := d}) in
      propagate_ports η (affected_ports.sort (≤))
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