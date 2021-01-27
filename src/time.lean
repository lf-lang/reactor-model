import network.basic
import data.rel

def tpm := finset (tag × option empty)

structure action_port_edge := 
  (src : port.id)
  (dst : port.id)

def finset.are_well_formed (es : finset action_port_edge) : Prop :=
  ∀ e e' : action_port_edge, e ∈ es → e' ∈ es → 
    e.src = e'.src → e = e'

def finset.are_separate_from (es : finset action_port_edge) (n : network) : Prop :=
  ∀ (e : action_port_edge) (e' : network.graph.edge), e ∈ es → e' ∈ n.η → 
    e.dst ≠ e'.src ∧ e.src ≠ e'.dst

structure timed_network :=
  (n : network)
  (time : tag)
  (event_queue : list tag)
  (action_ports : finset action_port_edge)
  (ap_well_formed : action_ports.are_well_formed)
  (ap_separate : action_ports.are_separate_from n)

-- The topo behaves as the reaction queue.
/-noncomputable def run_event (n : network) (t : list reaction.id) (eₕ : event) (eₜ : list event) : network :=
  {
    η := (run_topo n.η t).empty_ports,
    unique_ins := run_topo_unique_ports_inv n t,
    prec_acyclic := run_topo_prec_acyc_inv n t,
    time := eₕ.tag,
    event_queue := eₜ
  }
-/