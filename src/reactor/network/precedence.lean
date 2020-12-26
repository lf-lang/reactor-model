import data.rel
import reactor.basic
import reactor.network.basic

namespace reactor 
namespace network
namespace «precedence» 

  private def reaction_idx {c : ℕ} (n : network c) := Σ r : fin c, fin (n.φ.reactors r).reactions.length

  structure graph {c : ℕ} (n : reactor.network c) :=
    (reactions : reaction_idx n → reaction)
    (connects : rel (reaction_idx n) (reaction_idx n))

  namespace graph

    def is_topo_order_of {c : ℕ} {n : network c} (l : list (reaction_idx n)) (g : precedence.graph n) :=
      ∀ r r' : reaction_idx n, (g.connects r r') → (l.index_of r < l.index_of r')

  end graph

end «precedence»
end network
end reactor