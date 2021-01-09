import network.graph
import network.precedence

open network

def network.precedence_constraints {c : ℕ} (n : network.graph c) : Prop :=
  ∃ g : precedence.graph n, g.is_well_formed ∧ g.is_acyclic

structure network (c : ℕ) :=
  (depiction : network.graph c)
  (unique_ins : depiction.has_unique_port_ins)
  (constraints : network.precedence_constraints depiction)
