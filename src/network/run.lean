import digraph
import network.basic
import network.precedence
import network.ids

namespace network

  structure prec_func :=
    (func : network → precedence.graph)
    (well_formed : ∀ n, (func n).is_well_formed_over n.η)

  instance prec_func_coe : has_coe_to_fun prec_func := 
    ⟨_, (λ f, f.func)⟩

  structure topo_func :=
    (func : precedence.graph → list reaction.id)
    (is_topo : ∀ (n : network) (ρ : precedence.graph) (h : ρ.is_well_formed_over n.η), ρ.topological_order (n.prec_acyclic ρ h) (func ρ))

  instance topo_func_coe : has_coe_to_fun topo_func := 
    ⟨_, (λ f, f.func)⟩

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
          let ps := rcn rtr.input rtr.state in
          let rtr' := {reactor . output := ps.1, state := ps.2, ..rtr} in
          let η' : network.graph := η.update_data idₕ.rtr rtr' in
          let affected_ports := rcn.dₒ.image (λ d, {port.id . rtr := idₕ.rtr, prt := d}) in
          propagate_output η affected_ports
        else
          nₜ
    )

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

  lemma run_topo_unique_ports_inv (η : network.graph) (topo : list reaction.id) : 
    (run_topo η topo).has_unique_port_ins :=
    sorry

  lemma run_topo_prec_acyc_inv (η : network.graph) (topo : list reaction.id) : 
    (run_topo η topo).is_prec_acyclic :=
    sorry

  -- Why do we choose to define a specific run-func instead of describing propositionally, what the
  -- output of such a function should look like?
  -- Because in this case it's easier to define the function, than it's properties.
  noncomputable def run (n : network) (prec_func : prec_func) (topo_func : topo_func) : network :=
    let topo := topo_func (prec_func n) in
    let η' := run_topo n.η topo in
    { network .
      η := η',
      unique_ins := run_topo_unique_ports_inv n.η topo,
      prec_acyclic := run_topo_prec_acyc_inv n.η topo
    }

  theorem run_topo_indep (η : network.graph) (ρ : precedence.graph) (h_a : ρ.is_acyclic) (h_w : ρ.is_well_formed_over η) :
    ∃! output, ∀ (topo : list reaction.id) (_ : ρ.topological_order h_a topo), run_topo η topo = output :=
    sorry

  theorem determinism (n : network) (p p' : prec_func) (t t' : topo_func) :
    n.run p t = n.run p' t' := 
    sorry
    -- There are two components to this proof:
    --
    -- (1) Showing that the specific `prec_func` doesn't matter can be done by showing that all
    --    (well-formed!) `prec_func`s (for a given) `c` are equal.
    --    This hinges on the fact that for any given network there exists exactly one well-formed
    --    precedence graph. So if a `prec_func` wants to be well-formed, it has to return this
    --    exact precedence graph - hence, there really only exists *one* well-formed `prec_func`.
    --
    -- (2) Showing that the specific `topo_func` doesn't matter, will be tied to `run` itself.
    --     I.e. it's a quirk of `run` that the specific `topo_func` doesn't matter.
    --     This fact is captured by the theorem `run_topo_indep`.

end network