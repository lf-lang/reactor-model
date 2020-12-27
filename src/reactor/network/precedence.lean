import data.rel
import digraph
import reactor.network.basic

namespace reactor 
namespace network
namespace «precedence» 

  private structure reaction_index {c : ℕ} (n : fin c → reactor) := 
    (rtr : fin c)
    (rcn : fin (n rtr).nᵣ)
  
  structure graph.edge {c : ℕ} {n : fin c → reactor} (_ : reaction_index n → reaction) := 
    (src : reaction_index n)
    (dst : reaction_index n)

  instance prec_graph_edge {c : ℕ} {n : fin c → reactor} {r : reaction_index n → reaction} : digraph.edge (graph.edge r) reaction := 
    {
      src := (λ e, r e.src), 
      dst := (λ e, r e.dst)
    }

  def graph {c : ℕ} (n : network c) := digraph (reaction_index n.φ.nodes) reaction graph.edge

  namespace graph

    /-def is_topo_order_of {c : ℕ} {n : network c} (l : list (reaction_idx n)) (g : precedence.graph n) :=
      ∀ r r' : reaction_idx n, (g.connects r r') → (l.index_of r < l.index_of r')-/

  end graph

end «precedence»
end network
end reactor