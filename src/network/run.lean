import digraph
import network.basic
import network.precedence
import network.ids
import network.algorithms

namespace network

  noncomputable def propagate_edge (σ : network) : {n // n ≈ σ} → {e // e ∈ σ} → {n // n ≈ σ} := λ n e,
    {
      val := (n : network).update_input (e : graph.edge).dst ((n : network).η.output (e : graph.edge).src),
      property := trans_of (≈) (update_input_equiv n _ _) (n.property)
    }

  lemma r_comm_prop_edge : 
    ∀ σ, right_commutative (propagate_edge σ) :=
    begin
      unfold right_commutative,
      intros σ n e e',
      by_cases (e : graph.edge) = ↑e',
        rw (subtype.eq h),
        {
          have hₑ  : ↑e  ∈ (n : network), from edge_mem_equiv_trans n.property e.property,
          have hₑ' : ↑e' ∈ (n : network), from edge_mem_equiv_trans n.property e'.property,
          have hᵤ, from (n : network).unique_ins,
          rw graph.has_unique_port_ins at hᵤ,
          replace h : ↑e ≠ ↑e' := by exact h,
          have h_d : (e : graph.edge).dst ≠ (e' : graph.edge).dst, from hᵤ _ _ hₑ hₑ' h,
          unfold propagate_edge,
          simp,
          sorry
        }
    end

  noncomputable def propagate_port (n : network) (p : port.id) : network :=
    ↑((n.edges_out_of p).val.foldl (propagate_edge _) (r_comm_prop_edge _) ⟨n, refl _⟩)

  lemma r_comm_prop_port : right_commutative propagate_port :=
    sorry

  private noncomputable def propagate_ports (n : network) (p : finset port.id) : network :=
    p.val.foldl propagate_port r_comm_prop_port n 

  private noncomputable def propagate_output (n : network) (i : reaction.id) : network :=
    propagate_ports n ((n.η.rcn i).dₒ.image (λ d, {port.id . rtr := i.rtr, prt := d}))

  private noncomputable def run_reaction (n : network) (i : reaction.id) : network :=
    propagate_output (n.update_reactor i.rtr ((n.η.rtr i.rtr).run i.rcn) (reactor.run_equiv _ _)) i
      
  private noncomputable def run_topo : network → list reaction.id → network
    | n [] := n
    | n (topoₕ :: topoₜ) := run_topo (run_reaction n topoₕ) topoₜ

  -- Why do we choose to define a specific run-func instead of describing propositionally, what the
  -- output of such a function should look like?
  -- Because in this case it's easier to define the function, than it's properties.
  noncomputable def run (n : network) (prec_func : prec_func) (topo_func : topo_func) : network :=
    run_topo n (topo_func (prec_func n))

  theorem run_topo_indep (n : network) (ρ : precedence.graph) (h_a : ρ.is_acyclic) (h_w : ρ.is_well_formed_over n.η) :
    ∃! output, ∀ (topo : list reaction.id) (_ : ρ.topological_order h_a topo), run_topo n topo = output :=
    sorry

  theorem determinism (n : network) (p p' : prec_func) (t t' : topo_func) :
    n.run p t = n.run p' t' := 
    begin
      rw all_prec_funcs_are_eq p p',
      sorry
      -- Showing that the specific `topo_func` doesn't matter, will be tied to `run` itself.
      -- I.e. it's a quirk of `run` that the specific `topo_func` doesn't matter.
      -- This fact is captured by the theorem `run_topo_indep`.
    end

end network