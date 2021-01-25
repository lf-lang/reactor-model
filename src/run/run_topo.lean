import network.basic
import run.run_reaction
import precedence.lemmas

open network

noncomputable def run_topo : network.graph → list reaction.id → network.graph :=
  list.foldl run_reaction

lemma run_topo_equiv (η : network.graph) (t : list reaction.id) :
  run_topo η t ≈ η :=
  begin
    induction t with tₕ tₜ hᵢ generalizing η,
      case list.nil {
        unfold run_topo,
        exact refl_of (≈) η
      },
      case list.cons {
        unfold run_topo,
        have hₑ, from run_reaction_equiv η tₕ,
        have hᵢ', from hᵢ (run_reaction η tₕ),
        exact trans_of (≈) hᵢ' hₑ
      }
  end

lemma run_topo_unique_ports_inv (n : network) (topo : list reaction.id) : 
  (run_topo n.η topo).has_unique_port_ins :=
  begin
    have h, from run_topo_equiv n.η topo,
    exact network.graph.edges_inv_unique_port_ins_inv (symm h).left n.unique_ins
  end 
  
lemma run_topo_prec_acyc_inv (n : network) (topo : list reaction.id) : 
  (run_topo n.η topo).is_prec_acyclic :=
  begin
    have h, from run_topo_equiv n.η topo,
    exact network.graph.equiv_prec_acyc_inv (symm h) n.prec_acyclic
  end 

-- General proof : pulling a completely independent element out of the list to the front does not change the behaviour of run_topo.
lemma run_topo_swap 
{η : network.graph} (hᵤ : η.has_unique_port_ins) 
{ρ : precedence.graph} (h_a : ρ.is_acyclic) (h_wf : ρ.is_well_formed_over η)
(t : list reaction.id) (hₜ : digraph.is_topological_order t h_a) 
(i : reaction.id) (h_ti : i ∈ t) (hᵢ : digraph.fully_indep i t ρ) :
  run_topo η t = run_topo η (i :: (t.erase i)) :=
  begin
    -- (A.1) If `hd :: tl` is a topological order, then `hd` must be independent of all elements in `tl`. 
            -- (A.2) Adding a completely independent element to the front of a topo still gives you a topologically ordered list.
            -- (A.3) From (A.1) and `t = (t_hd :: t_tl)` and since `t` is a topo, it follows that `t_hd` is completely independent.
            -- (A.4) Since `t ~ t'` they contain the same elements, so `t_hd` is also completely indep of all elements in `t'.erase t_hd`.
            -- (A.5) From (A.2) it follows that `t_hd :: (t'.erase t_hd)` is topologically ordered.
            -- (A.6) 

            -- (A.3) Since `t' ~ (t_hd :: t_tl)`, `t'` not be empty, so `t' = t'_hd :: t'_tl`
            have : ∃ t'_hd t'_tl, t' = t'_hd :: t'_tl, from sorry,
            -- (A.4) Hence `run_topo η t' = run_topo η (t'_hd :: t'_tl)` and transitively
            have : ∃ t'_hd t'_tl, run_topo η t' = run_topo η (t'_hd :: t'_tl), from sorry,
            sorry
  end

theorem run_topo_comm (η : network.graph) (hᵤ : η.has_unique_port_ins) (ρ : precedence.graph) (h_a : ρ.is_acyclic) (h_wf : ρ.is_well_formed_over η) :
  ∀ (t t') (h_t : digraph.is_topological_order t h_a) (h_t' : digraph.is_topological_order t' h_a) (hₚ : t ~ t'), run_topo η t = run_topo η t' :=
  begin
    intros t t' h_t h_t' hₚ,
    induction t generalizing t' η,
      rw list.perm.eq_nil (list.perm.symm hₚ),
      {
        have h_e, from run_reaction_equiv η t_hd,
        have h_pe, from list.cons_perm_iff_perm_erase.mp hₚ, 
        have h_tc, from (digraph.topo_cons t_hd t_tl h_a h_t),
        have hte' : digraph.is_topological_order (t'.erase t_hd) h_a, from digraph.topo_erase t_hd t' h_a h_t',
        have htep' : t_tl ~ (t'.erase t_hd), from h_pe.right,
        have hᵤ' : (run_reaction η t_hd).has_unique_port_ins, from network.graph.edges_inv_unique_port_ins_inv (symm h_e).left hᵤ,
        have h_wf' : ρ.is_well_formed_over (run_reaction η t_hd), from network.graph.equiv_wf h_e h_wf,
        have h_fi : digraph.fully_indep t_hd t' ρ, {
          have h_fi₁ : digraph.fully_indep t_hd (t_hd :: t_tl) ρ, from digraph.topo_head_fully_indep _ _ h_a h_t,
          exact digraph.fully_indep_perm t_hd h_a h_t h_t' hₚ h_fi₁,
        }, 
        have hₘ : t_hd ∈ t', from h_pe.left,
        rw (run_topo_swap hᵤ h_a h_wf t' h_t' t_hd hₘ h_fi),
        unfold run_topo,
        repeat { rw list.foldl_cons },
        exact t_ih h_tc (t'.erase t_hd) (run_reaction η t_hd) hᵤ' h_wf' hte' htep'
      }
  end
