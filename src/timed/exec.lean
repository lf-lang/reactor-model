import timed.basic

open reactor.ports

-- !!! This shouldn't exist.

variables {υ : Type*} [decidable_eq υ]

def reactor.ports.clear_excluding {υ} [decidable_eq υ] (p : reactor.ports υ) (e : finset ℕ) : reactor.ports υ :=
  p.enum.map (λ iv, if (iv.1 ∈ e) then iv.2 else none)

def reactor.clear_ports_excluding (rtr : reactor υ) (i : finset ℕ) (o : finset ℕ) : reactor υ :=
  {input := rtr.input.clear_excluding i, output := rtr.output.clear_excluding o, ..rtr}

noncomputable def inst.network.graph.clear_reactor_excluding (η : inst.network.graph υ) (r : reactor.id) (i : finset port.id) (o : finset port.id) : inst.network.graph υ :=
  η.update_reactor r ((η.rtr r).clear_ports_excluding (i.image (λ x, x.prt)) (o.image (λ x, x.prt)))

noncomputable def inst.network.graph.clear_ports_excluding (η : inst.network.graph υ) (i : finset port.id) (o : finset port.id) : inst.network.graph υ :=
  η.ids.val.to_list.foldl (λ η' r, η'.clear_reactor_excluding r (i.filter (λ x, x.rtr = r)) (o.filter (λ x, x.rtr = r))) η

noncomputable def inst.network.clear_ports_excluding (n : inst.network υ) (i : finset port.id) (o : finset port.id) : inst.network υ :=
{
  η := n.η.clear_ports_excluding i o,
  unique_ins := sorry, -- TIME
  prec_acyclic := sorry -- TIME
}

namespace timed_network
  
  def priority_pred (σ : inst.network tpa) (e e' : action_edge) : Prop :=
    match priority_of e σ, priority_of e' σ with
    | _,      none    := true
    | none,   _       := true
    | some p, some p' := p ≥ p'
    end

  instance {n : inst.network tpa} : is_total action_edge (priority_pred n) := sorry
  instance {n : inst.network tpa} : is_antisymm action_edge (priority_pred n) := sorry
  instance {n : inst.network tpa} : is_trans action_edge (priority_pred n) := sorry
  instance {n : inst.network tpa} : decidable_rel (priority_pred n) := sorry

  def merge_tpas : option tpa → option tpa → tpa
    |  none     none     := ∅
    | (some t)  none     := t
    |  none    (some t') := t'
    | (some t) (some t') := t ∪ (t'.filter (λ tv', ∀ tv : (tag × option empty), tv ∈ t → tv.1 ≠ tv'.1))

  -- In this context "propagating" means consuming the source value, i.e. setting it to `none` once used.
  noncomputable def propagate_tpa (σ : inst.network tpa) (e : action_edge) : inst.network tpa :=
    (σ.update_port role.input e.iap (merge_tpas (σ.η.port reactor.ports.role.input e.iap) (σ.η.port reactor.ports.role.output e.oap)))
      .update_port role.output e.oap none

  noncomputable def gather_iap (as : finset action_edge) (σ : inst.network tpa) (p : port.id) : inst.network tpa :=
    ((as
      .filter (λ a : action_edge, a.iap = p))
      .sort (priority_pred σ))
      .foldl propagate_tpa σ

  noncomputable def propagate_actions (n : timed_network) : inst.network tpa :=
    n.input_action_ports.val.to_list.foldl (gather_iap n.actions) n.σ

  def tpa_at_tag (tpm : option tpa) (t : tag) : option tpa :=
    match tpm with 
      | none := none
      | some s := 
        let tpm' := s.filter (λ tv : tag × option empty, tv.1 = t) in
        if tpm' = ∅ then none else some tpm'
    end

  noncomputable def reduce_input_to_tag (t : tag) (σ : inst.network tpa) (i : port.id) : inst.network tpa :=
    σ.update_port role.input i (tpa_at_tag (σ.η.port reactor.ports.role.input i) t)

  noncomputable def at_tag (σ : inst.network tpa) (iaps : finset port.id) (t : tag) : inst.network tpa :=  
    iaps.val.to_list.foldl (reduce_input_to_tag t) σ 

  noncomputable def ports_for_actions (actions : finset action_edge) : finset port.id × finset port.id :=
    let ps := actions.image (λ e : action_edge, (e.iap, e.oap)) in
    (ps.image prod.fst, ps.image prod.snd)

  noncomputable def run_inst (σ : inst.network tpa) (fₚ : prec_func tpa) (tₚ : topo_func tpa) (actions : finset action_edge) : inst.network tpa :=
    let ⟨i, o⟩ := ports_for_actions actions in (σ.run fₚ tₚ).clear_ports_excluding i o

  noncomputable def inherit_iaps_from (σ σ' : inst.network tpa) (iaps : finset port.id) : inst.network tpa :=
    iaps.val.to_list.foldl (λ s i, s.update_port role.input i (σ'.η.port reactor.ports.role.input i)) σ

  noncomputable def events_for (σ : inst.network tpa) (aops : finset port.id) : finset tag :=
    aops.bind (λ p, let o := σ.η.port reactor.ports.role.output p in o.elim ∅ (finset.image prod.fst))

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