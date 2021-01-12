import network.graph
import network.precedence

open network

structure network :=
  (η : network.graph)
  (unique_ins : η.has_unique_port_ins)
  (prec_acyclic : η.is_prec_acyclic) -- In the long term this should be temporary.