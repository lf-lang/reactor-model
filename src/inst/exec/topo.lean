import topo
import inst.exec.propagate
import inst.prec
open reactor
open reactor.ports

-- Cf. inst/primitives.lean
variables {υ : Type*} [decidable_eq υ]

namespace inst
namespace network
namespace graph

  noncomputable def run_reaction (η : graph υ) (i : reaction.id) : graph υ :=
    (η.run_local i).propagate_ports ((η.run_local i).index_diff η i.rtr role.output).val.to_list
    
  -- Running a reaction is a network graph produces an equivalent network graph.
  lemma run_reaction_equiv (η : graph υ) (i : reaction.id) : run_reaction η i ≈ η :=
    begin
      unfold run_reaction,
      transitivity,
        exact propagate_ports_equiv _ _,
        exact run_local_equiv _ _,
    end

  -- Running a reaction retains relative equality for all other reactors, if ???.
  lemma run_reaction_eq_rel_to (η : graph υ) {i i' : reaction.id} (h : i.rtr ≠ i'.rtr) (h' : true) :
    (η.run_reaction i).rtr i'.rtr =i'.rcn= η.rtr i'.rtr :=
    begin
        suffices hg : ∀ p ∈ ((η.run_local i).index_diff η i.rtr role.output).val.to_list, ∀ e : edge, e ∈ (η.run_local i).eₒ p → e.dst ∉ (η.run_local i).deps i' role.input, 
        from eq_rel_to.multiple (propagate_ports_eq_rel_to hg) (run_local_eq_rel_to η h),

        simp only [multiset.mem_to_list, ←finset.mem_def],
        intros p hₚ e hₑ,
        simp only [eₒ, finset.mem_filter] at hₑ,
        have hₛ, from hₑ.right, 
        unfold index_diff at hₚ, 
        simp only [deps, reaction.deps, finset.mem_image, not_exists],
        intros x hₓ,
        sorry
    end

  -- If there is no path between two reactions in a precedence graph, then they are independent,
  -- i.e. their order of execution doesn't matter.
  lemma run_reaction_comm {η : network.graph υ} (hᵤ : η.has_unique_port_ins) {ρ : prec.graph υ} (hw : ρ.is_well_formed_over η) {i i' : reaction.id} (hᵢ : ¬(i~ρ~>i')) (hᵢ' : ¬(i'~ρ~>i)) :
    (η.run_reaction i).run_reaction i' = (η.run_reaction i').run_reaction i :=
    begin
      by_cases hc : i = i',  
        rw hc,
        {
          have hₙ, from prec.graph.indep_rcns_neq_rtrs hw hc hᵢ hᵢ',
          have hd, from prec.graph.indep_rcns_not_ext_dep hw hc hᵢ,
          have hd', from prec.graph.indep_rcns_not_ext_dep hw (ne.symm hc) hᵢ',
          unfold run_reaction,
          
          have hₑ, from run_reaction_eq_rel_to η hₙ true.intro,
          have hₑ', from run_reaction_eq_rel_to η (ne.symm hₙ) true.intro,
          rw run_reaction at hₑ hₑ',
          rw [run_local_index_diff_eq_rel_to hₑ, run_local_index_diff_eq_rel_to hₑ'],



          rw @propagate_ports_run_local_comm _ _ (η.run_local i) ((η.run_local i).index_diff η i.rtr role.output).val.to_list i' sorry,
          -- (run i) (run i') (prop i) (prop i')
          
          rw run_local_comm η hₙ,
          -- (run i') (run i) (prop i) (prop i')
          have hq, from equiv_trans (run_local_equiv (η.run_local i') i) (run_local_equiv η i'),
          unfold has_unique_port_ins at hᵤ,
          rw ←hq.left at hᵤ,
          rw propagate_ports_comm _ _ hᵤ,
          -- (run i') (run i) (prop i') (prop i)

          rw ←(@propagate_ports_run_local_comm _ _ (η.run_local i') ((η.run_local i').index_diff η i'.rtr role.output).val.to_list) i sorry,
          -- (run i') (prop i') (run i) (prop i)
        }
    end







noncomputable def run_topo (η : graph υ) (t : list reaction.id) : graph υ :=
  t.foldl run_reaction η

lemma run_topo_equiv (η : graph υ) (t : list reaction.id) :
  run_topo η t ≈ η :=
  begin
    induction t with tₕ tₜ hᵢ generalizing η,
      case list.nil {
        unfold run_topo,
        exact graph.equiv_refl η
      },
      case list.cons {
        unfold run_topo,
        have hₑ, from run_reaction_equiv η tₕ,
        have hᵢ', from hᵢ (run_reaction η tₕ),
        exact graph.equiv_trans hᵢ' hₑ
      }
  end

-- pulling a completely independent element out of the list to the front does not change the behaviour of run_topo.
lemma run_topo_swap 
{η : graph υ} (hᵤ : η.has_unique_port_ins) 
{ρ : prec.graph υ} (h_wf : ρ.is_well_formed_over η)
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
            have hᵤ' : (run_reaction η t_hd).has_unique_port_ins, 
            from graph.eq_edges_unique_port_ins (graph.equiv_symm h_e).left hᵤ,
            have h_wf' : ρ.is_well_formed_over (run_reaction η t_hd), 
            from network.graph.equiv_wf h_e h_wf,
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

theorem run_topo_comm (η : graph υ) (hᵤ : η.has_unique_port_ins) (ρ : prec.graph υ) (h_wf : ρ.is_well_formed_over η) :
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
        have hᵤ' : (run_reaction η t_hd).has_unique_port_ins, 
        from graph.eq_edges_unique_port_ins (graph.equiv_symm h_e).left hᵤ,
        have h_wf' : ρ.is_well_formed_over (run_reaction η t_hd), 
        from network.graph.equiv_wf h_e h_wf,
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

end graph
end network
end inst