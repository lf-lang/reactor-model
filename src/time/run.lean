import time.basic

namespace timed_network
  
  def priority_pred (σ : network tpa) (e e' : action_edge) : Prop :=
    match priority_of e σ, priority_of e' σ with
    | _,      none    := true
    | none,   _       := true
    | some p, some p' := p ≥ p'
    end

  instance {n : network tpa} : is_total action_edge (priority_pred n) := sorry
  instance {n : network tpa} : is_antisymm action_edge (priority_pred n) := sorry
  instance {n : network tpa} : is_trans action_edge (priority_pred n) := sorry
  instance {n : network tpa} : decidable_rel (priority_pred n) := sorry

  def merge_tpas : option tpa → option tpa → tpa
    |  none     none     := ∅
    | (some t)  none     := t
    |  none    (some t') := t'
    | (some t) (some t') := t ∪ (t'.filter (λ tv', ∀ tv : (tag × option empty), tv ∈ t → tv.1 ≠ tv'.1))

  -- In this context "propagating" means consuming the source value, i.e. setting it to `none` once used.
  noncomputable def propagate_tpa (σ : network tpa) (e : action_edge) : network tpa :=
    (σ.update_input e.iap (merge_tpas (σ.η.input e.iap) (σ.η.output e.oap)))
      .update_output e.oap none

  noncomputable def gather_input_action_port (as : finset action_edge) (σ : network tpa) (p : port.id) : network tpa :=
    ((as
      .filter (λ a : action_edge, a.iap = p))
      .sort (priority_pred σ))
      .foldl propagate_tpa σ

  noncomputable def propagate_actions (n : timed_network) : network tpa :=
    n.input_action_ports.val.to_list.foldl (gather_input_action_port n.actions) n.σ

  def tpa_at_tag (tpm : option tpa) (t : tag) : option tpa :=
    match tpm with 
      | none := none
      | some s := 
        let tpm' := s.filter (λ tv : tag × option empty, tv.1 = t) in
        if tpm' = ∅ then none else some tpm'
    end

  noncomputable def reduce_input_to_tag (t : tag) (σ : network tpa) (i : port.id) : network tpa :=
    σ.update_input i (tpa_at_tag (σ.η.input i) t)

  noncomputable def at_tag (σ : network tpa) (iaps : finset port.id) (t : tag) : network tpa :=  
    iaps.val.to_list.foldl (reduce_input_to_tag t) σ 

  noncomputable def ports_for_actions (actions : finset action_edge) : finset port.id × finset port.id :=
    let ps := actions.image (λ e : action_edge, (e.iap, e.oap)) in
    (ps.image prod.fst, ps.image prod.snd)

  noncomputable def run_inst (σ : network tpa) (fₚ : prec_func tpa) (tₚ : topo_func tpa) (actions : finset action_edge) : network tpa :=
    let ⟨i, o⟩ := ports_for_actions actions in (σ.run fₚ tₚ).clear_ports_excluding i o

  noncomputable def inherit_iaps_from (σ σ' : network tpa) (iaps : finset port.id) : network tpa :=
    iaps.val.to_list.foldl (λ s i, s.update_input i (σ'.η.input i)) σ

  noncomputable def events_for (σ : network tpa) (aops : finset port.id) : finset tag :=
    aops.bind (λ p, let o := σ.η.output p in o.elim ∅ (finset.image prod.fst))

  noncomputable def run_single (n : timed_network) (fₚ : prec_func tpa) (tₚ : topo_func tpa) : timed_network :=
    match n.event_queue with 
    | [] := n
    | hd :: tl := 
      let σ := n.propagate_actions in  
      let σ' := run_inst (at_tag σ n.input_action_ports hd) fₚ tₚ n.actions in
      { timed_network .
        σ := inherit_iaps_from σ' σ n.input_action_ports,
        time := hd,
        event_queue := (tl ++ (events_for σ' n.output_action_ports).val.to_list).merge_sort (≤),
        actions := n.actions,
        well_formed := sorry
      }
    end

end timed_network