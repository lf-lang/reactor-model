import network.graph
import precedence.basic

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

  lemma edge_mem_equiv_trans {n n' : network υ} {e : graph.edge} :
    n' ≈ n → e ∈ n → e ∈ n' :=
    begin
      intros hₑ hₘ,
      simp [(≈)] at hₑ,
      simp [(∈)],
      rw hₑ.left,
      apply hₘ
    end

  noncomputable def clear_ports_excluding (n : network υ) (i : finset port.id) (o : finset port.id) : network υ :=
    {
      η := n.η.clear_ports_excluding i o,
      unique_ins := sorry,
      prec_acyclic := sorry
    }

end network