import inst.network.graph
import inst.prec.basic
import inst.prec.lemmas

open reactor
open network

@[ext]
structure network (υ : Type*) [decidable_eq υ] :=
  (η : network.graph υ)
  (unique_ins : η.has_unique_port_ins)
  (prec_acyclic : η.is_prec_acyclic) -- In the long term this should be temporary.
  
variables {υ : Type*} [decidable_eq υ]

namespace network

  @[reducible]
  instance mem : has_mem graph.edge (network υ) := {mem := λ e n, e ∈ n.η.edges}

  instance equiv : has_equiv (network υ) := ⟨λ n n', n.η ≈ n'.η⟩

  instance : is_equiv (network υ) (≈) := 
    {
      symm := begin simp [(≈)], finish end,
      trans := begin simp [(≈)], finish end,
      refl := by simp [(≈)]
    }

  noncomputable def update_port (n : network υ) (r : ports.role) (p : port.id) (v : option υ) : network υ :=
    {
      η := n.η.update_port r p v,
      unique_ins := graph.eq_edges_unique_port_ins (refl _) n.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.equiv_symm (graph.update_port_equiv _ _ _ _)) n.prec_acyclic
    }

end network