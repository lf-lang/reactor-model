import topo
import inst.network.basic
import inst.exec.algorithms
import inst.exec.topo

-- Cf. inst/primitives.lean
variables {υ : Type*} [decidable_eq υ]

namespace inst
namespace network

  -- A helper function for `run`, that reassembles the result of `run_topo` into an `inst.network`.
  private noncomputable def run_aux (σ : inst.network υ) (t : list reaction.id) : inst.network υ :=
    {
      η := σ.η.run_topo t, 
      unique_ins := graph.eq_edges_unique_port_ins (symm (graph.run_topo_equiv σ.η t).left) σ.unique_ins, 
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.equiv_symm (graph.run_topo_equiv σ.η t)) σ.prec_acyclic
    }

  -- Runs a given instantaneous reactor network until its reaction queue is exhausted.
  -- The execution requires a function that generates a precedence graph for the network and 
  -- a function that can generate topological orderings over a directed acyclic graph.
  noncomputable def run (σ : inst.network υ) (fₚ : prec_func υ) (fₜ : topo_func υ) : inst.network υ :=
    run_aux σ (fₜ (fₚ σ))

  -- Running a network produces an equivalent network - i.e. its structure doesn't change.
  theorem run_equiv (σ : inst.network υ) (fₚ : prec_func υ) (fₜ : topo_func υ) : (σ.run fₚ fₜ).η ≈ σ.η :=
    by simp [run, run_aux, graph.run_topo_equiv]

  -- Running a network produces the same result, no matter which precedence- and topo-function are given.
  theorem determinism (σ : inst.network υ) (p p' : prec_func υ) (t t' : topo_func υ) : σ.run p t = σ.run p' t' := 
    begin
      rw prec_func.unique p p',
      unfold run run_aux,
      suffices h : σ.η.run_topo (t (p' σ)) = σ.η.run_topo (t' (p' σ)), by simp only [h],
      have hw, from p'.well_formed σ,
      have hₜ, from t.is_topo hw,
      have hₜ', from t'.is_topo hw,
      have hₚ, from topo.complete_perm hₜ hₜ',
      exact graph.run_topo_comm σ.unique_ins hw hₜ.left hₜ'.left hₚ
    end

end network
end inst