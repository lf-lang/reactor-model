import timed.basic
import inst.exec.run
open reactor
open reactor.ports
open inst.network

namespace timed
namespace network

  -- Propagates a TPA from its OAP to its IAP, by merging it into the IAP.
  -- In this context propagation implies *consuming* the source value, i.e. setting it to `none` once copied.
  noncomputable def propagate_tpa (σ : inst.network tpa) (e : action_edge) : inst.network tpa :=
    (σ.update_port role.input e.iap (tpa.merge (σ.η.port role.input e.iap) (σ.η.port role.output e.oap)))
    .update_port role.output e.oap none

  -- Propagating a TPA produces an equivalent instantanteous network.
  lemma propagate_tpa_equiv (σ : inst.network tpa) (e : action_edge) : propagate_tpa σ e ≈ σ :=
    begin
      unfold propagate_tpa,
      transitivity,
        exact update_port_equiv (σ.update_port role.input e.iap (tpa.merge (σ.η.port role.input e.iap) (σ.η.port role.output e.oap))) _ _ _,
        exact update_port_equiv σ _ _ _
    end

  -- Propagates the TPAs from all of the OAPs connected to a given IAP into the IAP.
  -- The signature of this function is a little strange, as to allow it to work for the fold in `propagate_actions`.
  noncomputable def gather_iap (as : finset action_edge) (σ : inst.network tpa) (iap : port.id) : inst.network tpa :=
    ((as.filter (λ a : action_edge, a.iap = iap)).val.to_list
        .merge_sort (action_priority_ge σ))
        .foldl propagate_tpa σ

  -- Gathering a IAP produces an equivalent instantanteous network.
  lemma gather_iap_equiv (as : finset action_edge) (σ : inst.network tpa) (iap : port.id) :
    gather_iap as σ iap ≈ σ :=
    begin
      unfold gather_iap,
      induction (as.filter (λ a : action_edge, a.iap = iap)).val.to_list.merge_sort (action_priority_ge σ) generalizing σ,
        case list.nil { simp },
        case list.cons {
          rw list.foldl_cons,
          transitivity,
            exact ih (propagate_tpa σ hd),
            exact propagate_tpa_equiv σ hd
        }
    end

  -- Propagates the TPAs from all OAPs to their respective IAPs.
  noncomputable def propagate_actions (σ : inst.network tpa) (iaps : finset port.id) (as : finset action_edge) : inst.network tpa :=
    iaps.val.to_list.foldl (gather_iap as) σ

  -- Propagating actions produces an equivalent instantanteous network.
  lemma propagate_actions_equiv (σ : inst.network tpa) (iaps : finset port.id) (as : finset action_edge) : 
    propagate_actions σ iaps as ≈ σ :=
    begin
      unfold propagate_actions,
      induction iaps.val.to_list generalizing σ,
        case list.nil { simp },
        case list.cons {
          rw list.foldl_cons,
          transitivity,
            exact ih (gather_iap as σ hd),
            exact gather_iap_equiv as σ hd
        }
    end

  -- Removes all tag-value pairs that are not at a given tag from a given IAP.
  -- The signature of this function is a little strange, as to allow it to work for the fold in `at_tag`.
  noncomputable def reduce_iap_to_tag (t : tag) (σ : inst.network tpa) (iap : port.id) : inst.network tpa :=
    σ.update_port role.input iap (tpa.at_tag (σ.η.port role.input iap) t)

  -- Reducing a IAP to a given tag produces an equivalent instantanteous network.
  lemma reduce_iap_to_tag_equiv (t : tag) (σ : inst.network tpa) (iap : port.id) : reduce_iap_to_tag t σ iap ≈ σ :=
    by { unfold reduce_iap_to_tag, exact update_port_equiv _ _ _ _ }

  -- Removes all tag-value pairs that are not at a given tag from all IAPs.
  noncomputable def at_tag (σ : inst.network tpa) (iaps : finset port.id) (t : tag) : inst.network tpa :=  
    iaps.val.to_list.foldl (reduce_iap_to_tag t) σ 

  -- Getting a network at a set tag produces an equivalent instantanteous network.
  lemma at_tag_equiv (σ : inst.network tpa) (iaps : finset port.id) (t : tag) : at_tag σ iaps t ≈ σ :=
    begin
      unfold at_tag,
      induction iaps.val.to_list generalizing σ,
        case list.nil { simp },
        case list.cons {
          rw list.foldl_cons,
          transitivity,
            exact ih (reduce_iap_to_tag t σ hd),
            exact reduce_iap_to_tag_equiv _ _ _
        }
    end

  -- Gets all of the tags contained in the TPAs of given ports.
  noncomputable def tags_in (σ : inst.network tpa) (ps : finset port.id) (r : ports.role) : finset tag :=
    ps.bUnion (λ p, (σ.η.port r p).elim ∅ (finset.image prod.fst))

  -- Returns the timed network that you get by running its next event (if there is one).
  noncomputable def run_event (τ : timed.network) (fₚ : prec_func tpa) (tₚ : topo_func tpa) : timed.network :=
    match τ.event_queue with 
    | [] := τ
    | hd :: tl := 
      let σ := propagate_actions τ.σ τ.iaps τ.actions in  
      let σᵣ := (at_tag σ τ.iaps hd).run fₚ tₚ in
      let σ' := (σᵣ.clear_all_ports.copy_ports σ τ.iaps role.input).copy_ports σᵣ τ.oaps role.output in
      { timed.network .
        σ := σ',
        time := hd,
        event_queue := (tl ++ (tags_in σ' τ.oaps role.output).val.to_list).merge_sort (≤),
        actions := τ.actions,
        well_formed := begin
          suffices h : (σᵣ.clear_all_ports.copy_ports σ τ.iaps role.input).copy_ports σᵣ τ.oaps role.output ≈ τ.σ, 
          from equiv_inst_network_wf τ.actions h τ.well_formed,
          iterate 6 { transitivity },
          iterate 2 { apply copy_ports_equiv },
          apply clear_all_ports_equiv, apply inst.network.run_equiv, apply at_tag_equiv, apply propagate_actions_equiv,
          refl
        end
      }
    end

end network
end timed