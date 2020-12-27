import data.rel
import digraph
import reactor.network.basic

namespace reactor 
namespace network
namespace «precedence» 

  private structure reaction_index {c : ℕ} (n : network c) := 
    (rtr : fin c)
    (rcn : fin (n.φ.nodes rtr).nᵣ)
  
  structure graph.edge {c : ℕ} {n : network c} (_ : reaction_index n → reaction) := 
    (src : reaction_index n)
    (dst : reaction_index n)

  instance prec_graph_edge {c : ℕ} {n : network c} {r : reaction_index n → reaction} : digraph.edge (graph.edge r) reaction := 
    {
      src := (λ e, r e.src), 
      dst := (λ e, r e.dst)
    }

  def graph {c : ℕ} (n : network c) := digraph (reaction_index n) reaction graph.edge

end «precedence»
end network
end reactor