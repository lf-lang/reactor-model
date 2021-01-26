import digraph
import network.basic
import run.algorithms
import run.event

namespace network

  private noncomputable def run_aux (n : network) (t : list reaction.id) : list event → network
    | [] := n
    | (eₕ :: eₜ) := run_event n t eₕ eₜ

  noncomputable def run (n : network) (fₚ : prec_func) (fₜ : topo_func) : network :=
    run_aux n (fₜ (fₚ n)) n.event_queue

  theorem run_equiv (n : network) (fₚ : prec_func) (fₜ : topo_func) :
    (n.run fₚ fₜ).η ≈ n.η :=
    begin
      unfold run run_aux,
      simp,
      apply run_topo_equiv
    end

  theorem determinism (n : network) (p p' : prec_func) (t t' : topo_func) :
    n.run p t = n.run p' t' := 
    begin
      rw all_prec_funcs_are_eq p p',
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