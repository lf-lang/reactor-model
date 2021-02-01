import topo
import network.basic  
import precedence.lemmas

variables (υ : Type*) [decidable_eq υ]

@[ext]
structure prec_func :=
  (func : network υ → precedence.graph υ)
  (well_formed : ∀ n, (func n).is_well_formed_over n.η)

instance prec_func_coe : has_coe_to_fun (prec_func υ) := 
  ⟨_, (λ f, f.func)⟩

theorem all_prec_funcs_are_eq : 
  ∀ p p' : prec_func υ, p = p' :=
  begin
    intros p p',
    have h_func : p.func = p'.func, {
      suffices h : ∀ n, p.func n = p'.func n, from funext h,
      intro n,
      have h_unique : ∃! ρ : precedence.graph _, ρ.is_well_formed_over n.η,
      from precedence.any_acyc_net_graph_has_exactly_one_wf_prec_graph n.η n.prec_acyclic,
      have h_wf, from p.well_formed n,
      have h_wf', from p'.well_formed n,
      exact exists_unique.unique h_unique h_wf h_wf'
    },
    exact prec_func.ext p p' h_func
  end

structure topo_func :=
  (func : precedence.graph υ → list reaction.id)
  (is_topo : ∀ (n : network υ) (ρ : precedence.graph υ) (h : ρ.is_well_formed_over n.η), (func ρ).is_complete_topo (n.prec_acyclic ρ h))

instance topo_func_coe : has_coe_to_fun (topo_func υ) := 
  ⟨_, (λ f, f.func)⟩