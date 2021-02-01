import time.basic

namespace timed_network
  
  def priority_pred (η : network.graph τ) (e e' : action_edge) : Prop :=
    match priority_of η e, priority_of η e' with
    | _,      none    := true
    | none,   _       := true
    | some p, some p' := p ≥ p'
    end

  instance {η : network.graph τ} : is_total action_edge (priority_pred η) := sorry
  instance {η : network.graph τ} : is_antisymm action_edge (priority_pred η) := sorry
  instance {η : network.graph τ} : is_trans action_edge (priority_pred η) := sorry
  instance {η : network.graph τ} : decidable_rel (priority_pred η) := sorry

  def merge_τs (o o' : option τ) (cutoff : tag) : option τ :=
    let t := match o, o' with
      | none,   none    := ∅
      | some t, none    := t
      | none,   some t' := t'
      | some t, some t' := t ∪ (t'.filter (λ tv', ∀ tv : (tag × option empty), tv ∈ t → tv.1 ≠ tv'.1))
    end in
    let o' := t.filter (λ tv, cutoff ≤ tv.1) in
    if o' = ∅ then none else some o'

  -- In this context "propagating" means consuming the source value, i.e. setting it to `none` once used.
  noncomputable def propagate_τ (cutoff : tag) (η : network.graph τ) (e : action_edge) : network.graph τ :=
    (η.update_input e.dst (merge_τs (η.input e.dst) (η.output e.src) cutoff))
      .update_output e.src none

  noncomputable def gather_input_action_port (cutoff : tag) (as : finset action_edge) (η : network.graph τ) (p : port.id) : network.graph τ :=
    ((as
      .filter (λ a : action_edge, a.dst = p))
      .sort (priority_pred η))
      .foldl (propagate_τ cutoff) η

  private noncomputable def at_tag_aux (n : timed_network) (t : tag) : network.graph τ :=
    n.input_action_ports.val.to_list.foldl (gather_input_action_port t n.actions) n.σ.η 

  lemma at_tag_aux_unique_ins {n : timed_network} (t : tag) :
    n.σ.η.has_unique_port_ins → (at_tag_aux n t).has_unique_port_ins :=
    sorry

  lemma at_tag_aux_prec_acyclic {n : timed_network} (t : tag) :
    n.σ.η.is_prec_acyclic → (at_tag_aux n t).is_prec_acyclic :=
    sorry

  noncomputable def at_tag (n : timed_network) (t : tag) : network τ :=
    {
      η := at_tag_aux n t,
      unique_ins := at_tag_aux_unique_ins t n.σ.unique_ins,
      prec_acyclic := at_tag_aux_prec_acyclic t n.σ.prec_acyclic
    }

  noncomputable def ports_for_actions (actions : finset action_edge) : finset port.id × finset port.id :=
    let ps := actions.image (λ e : action_edge, (e.dst, e.src)) in
    (ps.image prod.fst, ps.image prod.snd)

  noncomputable def run_inst (σ : network τ) (fₚ : prec_func τ) (tₚ : topo_func τ) (actions : finset action_edge) : network τ :=
    let ⟨i, o⟩ := ports_for_actions actions in (σ.run fₚ tₚ).clear_ports_excluding i o

  lemma run_inst_equiv (σ : network τ) (fₚ : prec_func τ) (tₚ : topo_func τ) (a : finset action_edge) :
    (run_inst σ fₚ tₚ a) ≈ σ :=
    sorry

  noncomputable def events_for (σ : network τ) (aops : finset port.id) : finset tag :=
    aops.bind (λ p, let o := σ.η.output p in o.elim ∅ (finset.image prod.fst))

  noncomputable def run_aux (n : timed_network) (fₚ : prec_func τ) (tₚ : topo_func τ) : list tag → timed_network
    | [] := n
    | (hd :: tl) := 
      let σ' := run_inst (n.at_tag hd) fₚ tₚ n.actions in
      {
        σ := σ',
        time := hd,
        event_queue := (tl ++ (events_for σ' n.output_action_ports).val.to_list).merge_sort (≤),
        actions := n.actions,
        well_formed := equiv_inst_net_wf_actions n σ' (run_inst_equiv _ _ _ _)
      }

  noncomputable def run (n : timed_network) (fₚ : prec_func τ) (tₚ : topo_func τ) : timed_network :=
    run_aux n fₚ tₚ n.event_queue

end timed_network