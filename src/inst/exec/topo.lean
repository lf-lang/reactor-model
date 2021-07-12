import topo
import inst.exec.propagate
import inst.network.prec
open reactor
open reactor.ports

-- Cf. inst/primitives.lean
variables {υ : Type*} [decidable_eq υ]

namespace inst
namespace network
namespace graph

  -- Runs a reaction in a network graph and propagates all of its affected output ports.
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

  -- A specialized version of `no_dep_no_eₒ_dep` for `run_reaction`.
  -- This is needed in the proof of `run_reaction_comm`.
  lemma run_reaction_no_path_no_eₒ_dep {η : graph υ} {ρ : prec.graph υ} (hw : ρ ⋈ η) {i i' : reaction.id} (hᵢ : ¬(i~ρ~>i')) (hₙ : i.rtr ≠ i'.rtr) (hₘ : i ∈ ρ.ids) (hₘ' : i' ∈ ρ.ids) :
    ∀ (p ∈ ((η.run_local i).index_diff η i.rtr role.output).val.to_list) (e : edge), (e ∈ (η.run_local i).eₒ p) → e.dst ∉ ((η.run_local i).deps i' role.input) ∧ (e.src ∉ (η.run_local i).deps i' role.output) :=
    begin
      intros p hₚ e hₑ,
      have hₛ, from index_diff_sub_dₒ η i,
      have h, from prec.graph.no_path_no_eₒ_dep hw hᵢ hₙ hₛ hₘ hₘ' p,      
      rw multiset.mem_to_list at hₚ,
      replace h := h hₚ e,
      have hq, from run_local_equiv η i,
      simp only [(≈)] at hq,
      unfold eₒ at hₑ,
      rw hq.left at hₑ,
      replace h := h hₑ,
      simp only [deps, rcn, (hq.right.right i'.rtr).right],
      exact h
    end

  -- If two reactions are independent, then their order of execution doesn't matter.
  -- The main part of the proof is the last line, which equates to:
  -- (run i)(run i')(prop i)(prop i') -> (run i')(run i)(prop i)(prop i') -> (run i')(run i)(prop i')(prop i) -> (run i')(prop i')(run i)(prop i)
  lemma run_reaction_comm {η : graph υ} (hᵤ : η.has_unique_port_ins) {ρ : prec.graph υ} (hw : ρ ⋈ η) {i i' : reaction.id} (hᵢ : ρ.indep i i') (hₘ : i ∈ ρ.ids) (hₘ' : i' ∈ ρ.ids) :
    (η.run_reaction i).run_reaction i' = (η.run_reaction i').run_reaction i :=
    begin
      by_cases hc : i = i',  
        rw hc,
        {
          have hₙ, from prec.graph.indep_rcns_neq_rtrs hw hc hᵢ hₘ hₘ',
          unfold run_reaction,
          have hd,  from run_reaction_no_path_no_eₒ_dep hw hᵢ.left hₙ hₘ hₘ',
          have hd', from run_reaction_no_path_no_eₒ_dep hw hᵢ.right (ne.symm hₙ) hₘ' hₘ,
          have hₑ,  from eq_rel_to.multiple (propagate_ports_eq_rel_to (by { intros p hₚ e hₑ, exact (hd  p hₚ e hₑ).left })) (run_local_eq_rel_to η hₙ),
          have hₑ', from eq_rel_to.multiple (propagate_ports_eq_rel_to (by { intros p hₚ e hₑ, exact (hd' p hₚ e hₑ).left })) (run_local_eq_rel_to η (ne.symm hₙ)),
          rw [run_local_index_diff_eq_rel_to hₑ, run_local_index_diff_eq_rel_to hₑ'],
          have hq, from equiv_trans (run_local_equiv (η.run_local i') i) (run_local_equiv η i'),
          unfold has_unique_port_ins at hᵤ,
          rw ←hq.left at hᵤ,
          rw [propagate_ports_run_local_comm hd, run_local_comm η hₙ, propagate_ports_comm _ _ hᵤ, ←(propagate_ports_run_local_comm hd')]
        }
    end

  -- Runs a given reaction queue on a network graph.
  noncomputable def run_topo (η : graph υ) (t : list reaction.id) : graph υ := 
    t.foldl run_reaction η

  -- Running a reaction queue produces an equivalent network graph.
  lemma run_topo_equiv (η : graph υ) (t : list reaction.id) : run_topo η t ≈ η :=
    begin
      induction t with tₕ tₜ hᵢ generalizing η,
        case list.nil { simp [run_topo] },
        case list.cons {
          unfold run_topo,
          transitivity,
            exact hᵢ (run_reaction η tₕ),
            exact run_reaction_equiv η tₕ
        }
    end

  -- Pulling a fully independent reaction out of a reaction queue and moving it to the front does not change the result of executing the queue.
  lemma run_topo_swap {η : graph υ} (hᵤ : η.has_unique_port_ins) {ρ : prec.graph υ} (h_w : ρ ⋈ η) {t : list reaction.id} (hₜ : t.is_topo_over ρ) {i : reaction.id} (h_ti : i ∈ t) (hᵢ : topo.indep i t ρ) (hₘ : ∀ i ∈ t, i ∈ ρ.ids) :
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
              have h_wf' : (ρ ⋈ run_reaction η t_hd), from equiv_wf_prec_inv h_e h_w,
              have hm' : ∀ i ∈ t_tl, i ∈ ρ.ids, { intros x hx, exact hₘ _ (list.mem_cons_of_mem t_hd hx) },
              have hᵢ', from @t_ih h_tc hm' i (run_reaction η t_hd) hᵤ' h_wf' h_ti' h_fi',
              have h_rr : run_topo (run_reaction η t_hd) t_tl = list.foldl run_reaction (run_reaction η t_hd) t_tl, from refl _,
              rw [←h_rr, hᵢ'],
              unfold run_topo,
              rw list.erase_cons_tail _ (ne.symm h_c),
              repeat { rw list.foldl_cons },
              have h_ind : topo.indep t_hd (t_hd :: t_tl) ρ, from topo.indep_head _ _ hₜ,
              unfold topo.indep at hᵢ h_ind,
              rw run_reaction_comm hᵤ h_w ⟨(hᵢ t_hd (list.mem_cons_self _ _)), (h_ind i h_ti)⟩ (hₘ _ (list.mem_cons_self _ _)) (hₘ _ h_ti)
            }     
        }
    end

  -- Executing different permutations of a reaction queue on a network graph, produces the same results as long as they're topologically ordered.
  theorem run_topo_comm {η : graph υ} (hᵤ : η.has_unique_port_ins) {ρ : prec.graph υ} (h_wf : ρ ⋈ η) :
    ∀ {t t' : list reaction.id} (h_t : t.is_topo_over ρ) (h_t' : t'.is_topo_over ρ) (hₚ : t ~ t') (hₘ : ∀ x ∈ t', x ∈ ρ.ids), run_topo η t = run_topo η t' :=
    begin
      intros t t' h_t h_t' hₚ hₘ,
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
          have h_wf' : (ρ ⋈ run_reaction η t_hd), from equiv_wf_prec_inv h_e h_wf,
          have h_fi : topo.indep t_hd t' ρ, {
            have h_fi₁ : topo.indep t_hd (t_hd :: t_tl) ρ, from topo.indep_head _ _ h_t,
            exact topo.indep_perm hₚ h_fi₁,
          }, 
          have hmt : t_hd ∈ t', from h_pe.left,
          rw (run_topo_swap hᵤ h_wf h_t' hmt h_fi hₘ),
          unfold run_topo, 
          repeat { rw list.foldl_cons },
          have hm' : ∀ x ∈ t'.erase t_hd, x ∈ ρ.ids, {  intros x hx, exact hₘ _ (list.mem_of_mem_erase hx) },
          exact t_ih h_tc hᵤ' h_wf' hte' htep' hm'
        }
    end

end graph
end network
end inst