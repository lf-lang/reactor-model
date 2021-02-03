import time.basic

namespace timed_network
  
  def priority_pred (σ : network τ) (e e' : action_edge) : Prop :=
    match priority_of e σ, priority_of e' σ with
    | _,      none    := true
    | none,   _       := true
    | some p, some p' := p ≥ p'
    end

  instance {n : network τ} : is_total action_edge (priority_pred n) := sorry
  instance {n : network τ} : is_antisymm action_edge (priority_pred n) := sorry
  instance {n : network τ} : is_trans action_edge (priority_pred n) := sorry
  instance {n : network τ} : decidable_rel (priority_pred n) := sorry

  def merge_τs : option τ → option τ → τ
    |  none     none     := ∅
    | (some t)  none     := t
    |  none    (some t') := t'
    | (some t) (some t') := t ∪ (t'.filter (λ tv', ∀ tv : (tag × option empty), tv ∈ t → tv.1 ≠ tv'.1))

  -- In this context "propagating" means consuming the source value, i.e. setting it to `none` once used.
  noncomputable def propagate_τ (σ : network τ) (e : action_edge) : network τ :=
    (σ.update_input e.dst (merge_τs (σ.η.input e.dst) (σ.η.output e.src)))
      .update_output e.src none

  noncomputable def gather_input_action_port (as : finset action_edge) (σ : network τ) (p : port.id) : network τ :=
    ((as
      .filter (λ a : action_edge, a.dst = p))
      .sort (priority_pred σ))
      .foldl propagate_τ σ

  noncomputable def propagate_actions (n : timed_network) : network τ :=
    n.input_action_ports.val.to_list.foldl (gather_input_action_port n.actions) n.σ

  def τ_at_tag (tpm : option τ) (t : tag) : option τ :=
    match tpm with 
      | none := none
      | some s := 
        let tpm' := s.filter (λ tv : tag × option empty, tv.1 = t) in
        if tpm' = ∅ then none else some tpm'
    end

  noncomputable def reduce_input_to_tag (t : tag) (σ : network τ) (i : port.id) : network τ :=
    σ.update_input i (τ_at_tag (σ.η.input i) t)

  noncomputable def at_tag (σ : network τ) (iaps : finset port.id) (t : tag) : network τ :=  
    iaps.val.to_list.foldl (reduce_input_to_tag t) σ 

  noncomputable def ports_for_actions (actions : finset action_edge) : finset port.id × finset port.id :=
    let ps := actions.image (λ e : action_edge, (e.dst, e.src)) in
    (ps.image prod.fst, ps.image prod.snd)

  noncomputable def run_inst (σ : network τ) (fₚ : prec_func τ) (tₚ : topo_func τ) (actions : finset action_edge) : network τ :=
    let ⟨i, o⟩ := ports_for_actions actions in (σ.run fₚ tₚ).clear_ports_excluding i o

  noncomputable def inherit_iaps_from (σ σ' : network τ) (iaps : finset port.id) : network τ :=
    iaps.val.to_list.foldl (λ s i, s.update_input i (σ'.η.input i)) σ

  noncomputable def events_for (σ : network τ) (aops : finset port.id) : finset tag :=
    aops.bind (λ p, let o := σ.η.output p in o.elim ∅ (finset.image prod.fst))

  noncomputable def run_aux (n : timed_network) (fₚ : prec_func τ) (tₚ : topo_func τ) : list tag → timed_network
    | [] := n
    | (hd :: tl) :=
      let σ := n.propagate_actions in  
      let σ' := run_inst (at_tag σ n.input_action_ports hd) fₚ tₚ n.actions in
      {
        σ := inherit_iaps_from σ' σ n.input_action_ports,
        time := hd,
        event_queue := (tl ++ (events_for σ' n.output_action_ports).val.to_list).merge_sort (≤),
        actions := n.actions,
        well_formed := sorry
      }

  noncomputable def run (n : timed_network) (fₚ : prec_func τ) (tₚ : topo_func τ) : timed_network :=
    run_aux n fₚ tₚ n.event_queue

end timed_network