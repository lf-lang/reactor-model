import digraph
import topo
import inst.network.basic
import inst.exec.algorithms
import inst.exec.topo

-- Cf. inst/primitives.lean
variables {υ : Type*} [decidable_eq υ]

namespace inst
namespace network

  -- A helper function for `run`, that reassembles the result of `run_topo` into an `inst.network`.
  private noncomputable def run_aux (n : inst.network υ) (t : list reaction.id) : inst.network υ :=
    {
      η := n.η.run_topo t, 
      unique_ins := graph.eq_edges_unique_port_ins (symm (graph.run_topo_equiv n.η t).left) n.unique_ins, 
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.equiv_symm (graph.run_topo_equiv n.η t)) n.prec_acyclic,
    }

  -- Runs a given instantaneous reactor network until its reaction queue is exhausted.
  -- The execution requires a function that generates a precedence graph for the network and 
  -- a function that can generate topological orderings over a directed acyclic graph.
  noncomputable def run (n : inst.network υ) (fₚ : prec_func υ) (fₜ : topo_func υ) : inst.network υ :=
    run_aux n (fₜ (fₚ n))

  -- Running a network produces an equivalent network - i.e. its structure doesn't change.
  theorem run_equiv (n : inst.network υ) (fₚ : prec_func υ) (fₜ : topo_func υ) : (n.run fₚ fₜ).η ≈ n.η :=
    by simp [run, run_aux, graph.run_topo_equiv]

  -- Running a network produces the same result, no matter which precedence- and topo-function are given.
  theorem determinism (n : inst.network υ) (p p' : prec_func υ) (t t' : topo_func υ) : n.run p t = n.run p' t' := 
    begin
      rw prec_func.all_eq p p',
      unfold run run_aux,
      suffices h : n.η.run_topo (t (p' n)) = n.η.run_topo (t' (p' n)), by simp only [h],
      have h_pnw, from p'.well_formed n,
      have h_t, from t.is_topo _ _ h_pnw,
      have h_t', from t'.is_topo _ _ h_pnw,
      have h_p, from topo.complete_perm h_t h_t',
      exact graph.run_topo_comm n.unique_ins h_pnw h_t.left h_t'.left h_p
    end

end network
end inst