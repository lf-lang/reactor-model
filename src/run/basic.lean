import digraph
import network.basic
import run.algorithms
import run.topo

variables {υ : Type*} [decidable_eq υ]

namespace network

 private noncomputable def run_aux (n : network υ) (t : list reaction.id) : network υ :=
    {η := run_topo n.η t, unique_ins := run_topo_unique_ports_inv n t, prec_acyclic := run_topo_prec_acyc_inv n t}

  noncomputable def run (n : network υ) (fₚ : prec_func υ) (fₜ : topo_func υ) : network υ :=
    run_aux n (fₜ (fₚ n))

  theorem run_equiv (n : network υ) (fₚ : prec_func υ) (fₜ : topo_func υ) :
    (n.run fₚ fₜ).η ≈ n.η :=
    begin
      unfold run run_aux,
      simp,
      apply run_topo_equiv
    end

  theorem determinism (n : network υ) (p p' : prec_func υ) (t t' : topo_func υ) :
    n.run p t = n.run p' t' := 
    begin
      rw all_prec_funcs_are_eq _ p p',
      unfold run run_aux,
      suffices h : run_topo n.η (t (p' n)) = run_topo n.η (t' (p' n)), {
        ext1,
        simp,
        exact h
      },
      have h_pnw : (p' n).is_well_formed_over n.η, from p'.well_formed n,
      have h_pna : (p' n).is_acyclic, from n.prec_acyclic (p' n) h_pnw,
      have h_t   : digraph.is_complete_topo_over (t (p' n)) (p' n) h_pna, from t.is_topo _ _ h_pnw,
      have h_t'  : digraph.is_complete_topo_over (t' (p' n)) (p' n) h_pna, from t'.is_topo _ _ h_pnw,
      have h_p   : (t (p' n)) ~ (t' (p' n)), from digraph.complete_topos_are_perm h_t h_t',
      exact run_topo_comm n.η n.unique_ins _ h_pna h_pnw _ _ h_t.left h_t'.left h_p
    end

end network