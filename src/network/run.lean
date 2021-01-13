import digraph
import network.basic
import network.precedence
import network.ids
import network.algorithms

namespace network

  -- For all edges `e` with `e.src = p`, set `e.dst` to `v`.  
  private noncomputable def propagate_port (η : network.graph) (p : port.id) (v : value) : network.graph := 
    let affected := η.edges.filter (λ e, e.src = p) in
    list.rec_on (affected.sort (≤)) η (λ eₕ _ η',
      let rtr := (η'.data eₕ.dst.rtr) in
      let input' := rtr.input.update_nth eₕ.dst.prt v in
      let rtr' := {reactor . input := input', ..rtr} in
      η'.update_data eₕ.dst.rtr rtr'
    )

  -- For all edges `e` with `e.src ∈ p`, set `e.dst` to `rtr.output.nth e.src`.  
  private noncomputable def propagate_output (η : network.graph) (p : finset port.id) : network.graph := 
    list.rec_on (p.sort (≤)) η (λ pₕ _ η', -- You can avoid `list` by using `finset.fold`.
      let v := option.join ((η.data pₕ.rtr).output.nth pₕ.prt) in
      v.elim η' (λ v', propagate_port η' pₕ v')
    ) 
      
  private noncomputable def run_topo (η : network.graph) (topo : list reaction.id) : network.graph :=
    list.rec_on topo η (λ idₕ _ nₜ,
      let rtr := nₜ.rtr idₕ in
      let rcn := nₜ.rcn idₕ in
        if rcn.fires_on rtr.input then
          let ⟨p', s'⟩ := rcn rtr.input rtr.state in
          let rtr' := {reactor . output := p', state := s', ..rtr} in
          let η' := η.update_data idₕ.rtr rtr' in
          let affected_ports := rcn.dₒ.image (λ d, {port.id . rtr := idₕ.rtr, prt := d}) in
          propagate_output η affected_ports
        else
          nₜ
    )

  theorem run_topo_equiv_net_graph (η : network.graph) (topo : list reaction.id) :
    η ≈ (run_topo η topo) :=
    sorry

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
    { network .
      η := η',
      unique_ins := run_topo_unique_ports_inv n topo,
      prec_acyclic := run_topo_prec_acyc_inv n topo
    }

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