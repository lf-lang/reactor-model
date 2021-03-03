import topo
import inst.network.basic
import inst.exec.reaction
import inst.prec.lemmas

open network

variables {υ : Type*} [decidable_eq υ]

noncomputable def run_topo : network.graph υ → list reaction.id → network.graph υ :=
  list.foldl run_reaction

lemma run_topo_equiv (η : network.graph υ) (t : list reaction.id) :
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

lemma run_topo_unique_ports_inv (n : network υ) (topo : list reaction.id) : 
  (run_topo n.η topo).has_unique_port_ins :=
  begin
    have h, from run_topo_equiv n.η topo,
    exact network.graph.edges_inv_unique_port_ins_inv (symm h).left n.unique_ins
  end 
  
lemma run_topo_prec_acyc_inv (n : network υ) (topo : list reaction.id) : 
  (run_topo n.η topo).is_prec_acyclic :=
  begin
    have h, from run_topo_equiv n.η topo,
    exact network.graph.equiv_prec_acyc_inv (symm h) n.prec_acyclic
  end 

-- pulling a completely independent element out of the list to the front does not change the behaviour of run_topo.
lemma run_topo_swap 
{η : network.graph υ} (hᵤ : η.has_unique_port_ins) 
{ρ : precedence.graph υ} (h_wf : ρ.is_well_formed_over η)
(t : list reaction.id) (hₜ : t.is_topo_over ρ) 
(i : reaction.id) (h_ti : i ∈ t) (hᵢ : topo.indep i t ρ) :
  run_topo η t = run_topo η (i :: (t.erase i)) :=
  begin
    induction t generalizing i η,
      { exfalso, exact h_ti },
      {
        unfold run_topo,
        repeat { rw list.foldl_cons },
        have h_tc, from (topo.cons_is_topo hₜ),
        by_cases h_c : i = t_hd,
          simp [h_c],
          {
            have h_e, from run_reaction_equiv η t_hd,
            have h_ti', from or.resolve_left (list.eq_or_mem_of_mem_cons h_ti) h_c,
            have h_fi', from topo.indep_cons hᵢ,
            have hᵤ' : (run_reaction η t_hd).has_unique_port_ins, from network.graph.edges_inv_unique_port_ins_inv (symm h_e).left hᵤ,
            have h_wf' : ρ.is_well_formed_over (run_reaction η t_hd), from network.graph.equiv_wf h_e h_wf,
            have hᵢ', from @t_ih h_tc i (run_reaction η t_hd) hᵤ' h_wf' h_ti' h_fi',
            have h_rr : run_topo (run_reaction η t_hd) t_tl = list.foldl run_reaction (run_reaction η t_hd) t_tl, from refl _,
            rw [←h_rr, hᵢ'],
            unfold run_topo,
            rw list.erase_cons_tail _ (ne.symm h_c),
            repeat { rw list.foldl_cons },
            have h_ind : topo.indep t_hd (t_hd :: t_tl) ρ, from topo.indep_head _ _ hₜ,
            unfold topo.indep at hᵢ h_ind,
            rw run_reaction_comm hᵤ h_wf (hᵢ t_hd (list.mem_cons_self _ _)) (h_ind i h_ti),
          }     
      }
  end

theorem run_topo_comm (η : network.graph υ) (hᵤ : η.has_unique_port_ins) (ρ : precedence.graph υ) (h_wf : ρ.is_well_formed_over η) :
  ∀ (t t' : list reaction.id) (h_t : t.is_topo_over ρ) (h_t' : t'.is_topo_over ρ) (hₚ : t ~ t'), run_topo η t = run_topo η t' :=
  begin
    intros t t' h_t h_t' hₚ,
    induction t generalizing t' η,
      rw list.perm.eq_nil (list.perm.symm hₚ),
      {
        have h_e, from run_reaction_equiv η t_hd,
        have h_pe, from list.cons_perm_iff_perm_erase.mp hₚ, 
        have h_tc, from (topo.cons_is_topo h_t),
        have hte' : (t'.erase t_hd).is_topo_over ρ, from topo.erase_is_topo _ h_t',
        have htep' : t_tl ~ (t'.erase t_hd), from h_pe.right,
        have hᵤ' : (run_reaction η t_hd).has_unique_port_ins, from network.graph.edges_inv_unique_port_ins_inv (symm h_e).left hᵤ,
        have h_wf' : ρ.is_well_formed_over (run_reaction η t_hd), from network.graph.equiv_wf h_e h_wf,
        have h_fi : topo.indep t_hd t' ρ, {
          have h_fi₁ : topo.indep t_hd (t_hd :: t_tl) ρ, from topo.indep_head _ _ h_t,
          exact topo.indep_perm hₚ h_fi₁,
        }, 
        have hₘ : t_hd ∈ t', from h_pe.left,
        rw (run_topo_swap hᵤ h_wf t' h_t' t_hd hₘ h_fi),
        unfold run_topo,
        repeat { rw list.foldl_cons },
        exact t_ih h_tc (t'.erase t_hd) (run_reaction η t_hd) hᵤ' h_wf' hte' htep'
      }
  end
