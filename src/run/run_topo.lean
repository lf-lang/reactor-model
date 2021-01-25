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

theorem run_topo_comm (η : network.graph) (hᵤ : η.has_unique_port_ins) (ρ : precedence.graph) (h_a : ρ.is_acyclic) (h_wf : ρ.is_well_formed_over η) :
  ∀ (t t') (h_t : digraph.is_topological_order t h_a) (h_t' : digraph.is_topological_order t' h_a) (hₚ : t ~ t'), run_topo η t = run_topo η t' :=
  begin
    intros t t' h_t h_t' hₚ,
    induction hₚ with generalizing η ρ,
      case list.perm.nil {
        refl,
      },
      case list.perm.cons {
        unfold run_topo,
        repeat { rw list.foldl_cons },
        have h_t_tl, from digraph.topo_cons hₚ_x hₚ_l₁ h_a h_t,
        have h_t'_tl, from digraph.topo_cons hₚ_x hₚ_l₂ h_a h_t',
        have h_e, from run_reaction_equiv η hₚ_x,
        have h_wf' : ρ.is_well_formed_over (run_reaction η hₚ_x), from network.graph.equiv_wf h_e h_wf,
        have hᵤ' : (run_reaction η hₚ_x).has_unique_port_ins, 
        from network.graph.edges_inv_unique_port_ins_inv (symm (run_reaction_equiv _ _).left) hᵤ,
        exact hₚ_ih (run_reaction η hₚ_x) ρ hᵤ' h_a h_wf' h_t_tl h_t'_tl
      },
      case list.perm.swap {
        obtain ⟨h_indep, h_indep'⟩ := digraph.topo_swap_indep hₚ_y hₚ_x hₚ_l h_a h_t h_t',
        unfold run_topo,
        repeat { rw list.foldl_cons }, 
        rw run_reaction_comm hᵤ h_wf h_indep h_indep'
      },
      case list.perm.trans : l1 l2 l3 hp1 hp2 hi1 hi2 {
        -- Is there away to force l2 into being a topological order
        -- or is it possible to use the induction hypotheses without that fact?
        have PROBLEM : digraph.is_topological_order l2 h_a, from sorry,
        have hi1', from hi1 η ρ hᵤ h_a h_wf h_t PROBLEM,
        have hi2', from hi2 η ρ hᵤ h_a h_wf PROBLEM h_t',
        exact trans hi1' hi2', 
      }
  end