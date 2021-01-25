import network.graph
import precedence.basic

open network

@[ext]
structure network :=
  (η : network.graph)
  (unique_ins : η.has_unique_port_ins)
  (prec_acyclic : η.is_prec_acyclic) -- In the long term this should be temporary.

namespace network

  @[reducible]
  instance mem : has_mem graph.edge network := {mem := λ e n, e ∈ n.η.edges}

  instance equiv : has_equiv network := ⟨λ n n', n.η ≈ n'.η⟩

  instance : is_equiv network (≈) := 
    {
      symm := begin simp [(≈)], finish end,
      trans := begin simp [(≈)], finish end,
      refl := by simp [(≈)]
    }

  lemma edge_mem_equiv_trans {n n' : network} {e : graph.edge} :
    n' ≈ n → e ∈ n → e ∈ n' :=
    begin
      intros hₑ hₘ,
      simp [(≈)] at hₑ,
      simp [(∈)],
      rw hₑ.left,
      apply hₘ
    end

end network