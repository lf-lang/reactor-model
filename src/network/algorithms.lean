import network.basic  

namespace network

  @[ext]
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

  theorem all_prec_funcs_are_eq : 
    ∀ p p' : prec_func, p = p' :=
    begin
      intros p p',
      have h_func : p.func = p'.func, {
        suffices h : ∀ n, p.func n = p'.func n, from funext h,
        intro n,
        have h_unique : ∃! ρ : precedence.graph, ρ.is_well_formed_over n.η,
          from precedence.any_acyc_net_graph_has_exactly_one_wf_prec_graph n.η n.prec_acyclic,
        have h_wf, from p.well_formed n,
        have h_wf', from p'.well_formed n,
        exact exists_unique.unique h_unique h_wf h_wf'
      },
      exact prec_func.ext p p' h_func
    end

end network