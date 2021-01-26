import run.topo

-- The topo behaves as the reaction queue.
noncomputable def run_event (n : network) (t : list reaction.id) (eₕ : event) (eₜ : list event) : network :=
  {
    η := (run_topo n.η t).empty_ports,
    unique_ins := run_topo_unique_ports_inv n t,
    prec_acyclic := run_topo_prec_acyc_inv n t,
    time := eₕ.tag,
    event_queue := eₜ
  }