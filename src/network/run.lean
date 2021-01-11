import network.basic
import network.precedence
import network.ids
import graphs.dag

namespace network

  variable {c : ℕ}

  structure prec_func (c : ℕ) :=
    (func : Π n : network c, precedence.graph n.φ)
    (well_formed : ∀ n, (func n).is_well_formed)

  instance prec_func_coe {c : ℕ} : has_coe_to_fun (prec_func c) := 
    ⟨_, (λ f, f.func)⟩

  structure topo_func {c : ℕ} (n : network c) :=
    (func : precedence.graph n.φ → list (reaction.id n.φ.data))
    (is_topo : ∀ (p : precedence.graph n.φ) (h : p.is_well_formed), dag.topological_order ⟨p, n.prec_acyclic p h⟩ (func p))

  instance topo_func_coe {c : ℕ} {n : network c} : has_coe_to_fun (topo_func n) := 
    ⟨_, (λ f, f.func)⟩

  private def propagating_output (n : network.graph c) (r : reaction.id n.data) : network.graph c :=
    sorry
    -- For all edges `e` with `e.src ∈ rcn.dₒ`, set `e.dst` to `rtr.output e.src`.  

  private noncomputable def run_topo (n : network.graph c) (topo : list (reaction.id n.data)) : network.graph c :=
    list.rec_on topo n (λ idₕ _ nₜ,
      let rtr := nₜ.data idₕ.rtr in
      let rcn := rtr.reactions idₕ.rcn in
      let hᵢ : rcn.nᵢ = rtr.nᵢ := sorry in
      let hₒ : rtr.nₒ = rcn.nₒ := sorry in
      let hᵣ : rcn.is_det := sorry in
      let i := rtr.input.cast hᵢ in
        if rcn.fires_on i then
          let ps := rcn.body.det hᵣ (i, rtr.state) in
          let rtr' := {reactor . output := ps.1.cast hₒ, state := ps.2, ..rtr} in
          let n' := n.setting idₕ.rtr rtr' in
          propagating_output n' idₕ
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

  lemma run_topo_unique_ports_inv (n : network.graph c) (topo : list (reaction.id n.data)) : 
    (run_topo n topo).has_unique_port_ins :=
    sorry

  lemma run_topo_prec_acyc_inv (n : network.graph c) (topo : list (reaction.id n.data)) : 
    network.is_prec_acyclic (run_topo n topo) :=
    sorry

  lemma run_topo_det_inv (n : network.graph c) (topo : list (reaction.id n.data)) :
    network.is_det (run_topo n topo) :=
    sorry

  -- Why do we choose to define a specific run-func instead of describing propositionally, what the
  -- output of such a function should look like?
  -- Because in this case it's easier to define the function, than it's properties.
  noncomputable def run (n : network c) (prec_func : prec_func c) (topo_func : topo_func n) : network c :=
    let topo := topo_func (prec_func n) in
    let φ' := run_topo n.φ topo in
    { network .
      φ := φ',
      unique_ins := run_topo_unique_ports_inv n.φ topo,
      prec_acyclic := run_topo_prec_acyc_inv n.φ topo,
      det := run_topo_det_inv n.φ topo
    }

  theorem run_topo_indep (n : network.graph c) (p : precedence.graph n) (h_a : p.is_acyclic) (h_w : p.is_well_formed) :
    ∃! output, ∀ (topo : list (reaction.id n.data)) (h : dag.topological_order ⟨p, h_a⟩ topo), 
      run_topo n topo = output :=
    sorry

  theorem determinism (n : network c) (p p' : prec_func c) (t t' : topo_func n) :
    run n p t = run n p' t' := 
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