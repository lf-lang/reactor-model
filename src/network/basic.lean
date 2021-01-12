import network.graph
import network.precedence

open network

-- The proposition, that every well-formed precedence graph over a network is acyclic.
def network.is_prec_acyclic (n : network.graph) : Prop :=
  ∀ p : precedence.graph, p.is_well_formed_over n → p.is_acyclic

-- The proposition, that a network graph only contains deterministic reactors.
def network.is_det (n : network.graph) : Prop :=
  ∀ r ∈ n.members, reactor.is_det r

structure network :=
  (φ : network.graph)
  (unique_ins : φ.has_unique_port_ins)
  (prec_acyclic : network.is_prec_acyclic φ) -- In the long term this should be temporary.
  (det : network.is_det φ) -- This should ultimately be temporary.