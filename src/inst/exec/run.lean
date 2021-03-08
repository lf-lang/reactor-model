import digraph
import topo
import inst.network.basic
import inst.exec.algorithms
import inst.exec.topo

variables {υ : Type*} [decidable_eq υ]

namespace inst.network

 private noncomputable def run_aux (n : inst.network υ) (t : list reaction.id) : inst.network υ :=
    {
      η := n.η.run_topo t, 
      unique_ins := graph.eq_edges_unique_port_ins (symm (graph.run_topo_equiv n.η t).left) n.unique_ins, 
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.equiv_symm (graph.run_topo_equiv n.η t)) n.prec_acyclic,
    }

  noncomputable def run (n : inst.network υ) (fₚ : prec_func υ) (fₜ : topo_func υ) : inst.network υ :=
    run_aux n (fₜ (fₚ n))

  theorem run_equiv (n : inst.network υ) (fₚ : prec_func υ) (fₜ : topo_func υ) : (n.run fₚ fₜ).η ≈ n.η :=
    by simp [run, run_aux, graph.run_topo_equiv]

  theorem determinism (n : inst.network υ) (p p' : prec_func υ) (t t' : topo_func υ) : n.run p t = n.run p' t' := 
    begin
      rw all_prec_funcs_are_eq _ p p',
      unfold run run_aux,
      suffices h : n.η.run_topo (t (p' n)) = n.η.run_topo (t' (p' n)), by simp only [h],
      have h_pnw : (p' n).is_well_formed_over n.η, from p'.well_formed n,
      have h_t   : (t (p' n)).is_complete_topo_over (p' n), from t.is_topo _ _ h_pnw,
      have h_t'  : (t' (p' n)).is_complete_topo_over (p' n), from t'.is_topo _ _ h_pnw,
      have h_p   : (t (p' n)) ~ (t' (p' n)), from topo.complete_perm h_t h_t',
      exact graph.run_topo_comm n.η n.unique_ins _ h_pnw _ _ h_t.left h_t'.left h_p
    end

end inst.network