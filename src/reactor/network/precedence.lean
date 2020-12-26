import data.rel
import digraph
import reactor.network.basic

namespace reactor 
namespace network
namespace «precedence» 

  private def reaction_idx {c : ℕ} (n : network c) := Σ r : fin c, fin (n.reactors r).reactions.length
  def graph.edge {c : ℕ} (n : network c) := (reaction_idx n) × (reaction_idx n)

  instance {c : ℕ} {n : network c} : digraph.edge (graph.edge n) reaction := 
    ⟨(λ e, (n.reactors e.1.1).reactions e.1.2), (λ e, (n.reactors e.2.1).reactions e.2.2)⟩

  def graph {c : ℕ} (r : fin c → reactor) := digraph (fin c) reactor (graph.edge r)

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