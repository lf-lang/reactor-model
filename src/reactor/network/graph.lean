import reactor.basic
import digraph

namespace reactor 
namespace network

  structure graph.edge {c : ℕ} (reactors : fin c → reactor) :=
    (src : Σ r : fin c, fin (reactors r).nₒ)
    (dst : Σ r : fin c, fin (reactors r).nᵢ)

  instance net_graph_edge {c : ℕ} {r : fin c → reactor} : digraph.edge (graph.edge r) reactor := 
    {
      src := (λ e, r e.src.1), 
      dst := (λ e, r e.dst.1)
    }

  def graph (c : ℕ) := digraph (fin c) reactor graph.edge

end network
end reactor

