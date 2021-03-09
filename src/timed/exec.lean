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
    let t := tpa.merge (σ.η.port role.input e.iap) (σ.η.port role.output e.oap) in
    (σ.update_port role.input e.iap t).update_port role.output e.oap none

  -- Propagates the TPAs from all of the OAPs connected to a given IAP into the IAP.
  -- The signature of this function is a little strange, as to allow it to work for the fold in `propagate_actions`.
  noncomputable def gather_iap (as : finset action_edge) (σ : inst.network tpa) (iap : port.id) : inst.network tpa :=
    ((as.filter (λ a : action_edge, a.iap = iap))
        .sort (action_edge_ge σ))
        .foldl propagate_tpa σ

  -- Propagates the TPAs from all OAPs to their respective IAPs.
  noncomputable def propagate_actions (τ : timed.network) : inst.network tpa :=
    τ.iaps.val.to_list.foldl (gather_iap τ.actions) τ.σ

  -- Removes all tag-value pairs that are not at a given tag from a given IAP.
  -- The signature of this function is a little strange, as to allow it to work for the fold in `at_tag`.
  noncomputable def reduce_iap_to_tag (t : tag) (σ : inst.network tpa) (iap : port.id) : inst.network tpa :=
    σ.update_port role.input iap (tpa.at_tag (σ.η.port role.input iap) t)

  -- Removes all tag-value pairs that are not at a given tag from all IAPs.
  noncomputable def at_tag (σ : inst.network tpa) (iaps : finset port.id) (t : tag) : inst.network tpa :=  
    iaps.val.to_list.foldl (reduce_iap_to_tag t) σ 

  -- Gets all of the tags contained in the TPAs of given ports.
  noncomputable def tags_in (σ : inst.network tpa) (ps : finset port.id) (r : ports.role) : finset tag :=
    ps.bUnion (λ p, (σ.η.port r p).elim ∅ (finset.image prod.fst))

  -- Returns the timed network that you get by running its next event (if there is one).
  noncomputable def run_event (τ : timed.network) (fₚ : prec_func tpa) (tₚ : topo_func tpa) : timed.network :=
    match τ.event_queue with 
    | [] := τ
    | hd :: tl := 
      let σ := τ.propagate_actions in  
      let σᵣ := (at_tag σ τ.iaps hd).run fₚ tₚ in
      let σ' := (σᵣ.clear_all_ports.copy_ports σ τ.iaps role.input).copy_ports σᵣ τ.oaps role.output in
      { timed.network .
        σ := σ',
        time := hd,
        event_queue := (tl ++ (tags_in σ' τ.oaps role.output).val.to_list).merge_sort (≤),
        actions := τ.actions,
        well_formed := sorry
      }
    end

end network
end timed