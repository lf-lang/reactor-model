import topo
import inst.network.basic 

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

namespace inst
namespace network

  -- A function that can generate a well-formed precedence graph for a given instantaneous network.
  @[ext]
  structure prec_func :=
    (func : inst.network υ → prec.graph υ)
    (well_formed : ∀ n, (func n) ⋈ n.η)

  -- A function that can generate a complete topological ordering for a given precedence graph.
  structure topo_func :=
    (func : prec.graph υ → list reaction.id)
    (is_topo : ∀ (n : inst.network υ) (ρ : prec.graph υ) (h : ρ ⋈ n.η), (func ρ).is_complete_topo_over ρ)

  variable {υ}

  -- Calling an instance of `prec_func` as a function, means calling its `func`.
  instance prec_func_coe : has_coe_to_fun (prec_func υ) := ⟨_, (λ f, f.func)⟩

  -- Calling an instance of `topo_func` as a function, means calling its `func`.
  instance topo_func_coe : has_coe_to_fun (topo_func υ) := ⟨_, (λ f, f.func)⟩

  -- All precedence functions are equal.
  theorem prec_func.all_eq (p p' : prec_func υ) : p = p' :=
    begin
      rw prec_func.ext p p',
      funext n,
      have h, from prec.prec_acyc_net_graph_has_exactly_one_wf_prec_graph n.prec_acyclic,
      exact exists_unique.unique h (p.well_formed n) (p'.well_formed n)
    end

end network
end inst
