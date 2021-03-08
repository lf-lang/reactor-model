import topo
import inst.network.basic  
import inst.prec

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

-- A function that can generate a well-formed precedence graph for a given instantaneous network.
@[ext]
structure prec_func :=
  (func : inst.network υ → prec.graph υ)
  (well_formed : ∀ n, (func n).is_well_formed_over n.η)

-- A function that can generate a complete topological ordering for a given precedence graph.
structure topo_func :=
  (func : prec.graph υ → list reaction.id)
  (is_topo : ∀ (n : inst.network υ) (ρ : prec.graph υ) (h : ρ.is_well_formed_over n.η), (func ρ).is_complete_topo_over ρ)

variable {υ}

-- Calling an instance of `prec_func` as a function, means calling its `func`.
instance prec_func_coe : has_coe_to_fun (prec_func υ) := ⟨_, (λ f, f.func)⟩

-- Calling an instance of `topo_func` as a function, means calling its `func`.
instance topo_func_coe : has_coe_to_fun (topo_func υ) := ⟨_, (λ f, f.func)⟩

-- All precedence functions are equal.
theorem prec_func.all_eq (p p' : prec_func υ) : p = p' :=
  begin
    suffices hg : p.func = p'.func, from prec_func.ext p p' hg,
    suffices h : ∀ n, p.func n = p'.func n, from funext h,
    intro n,
    have h_unique : ∃! ρ : prec.graph _, ρ.is_well_formed_over n.η,
    from prec.any_acyc_net_graph_has_exactly_one_wf_prec_graph n.η n.prec_acyclic,
    exact exists_unique.unique h_unique (p.well_formed n) (p'.well_formed n)
  end