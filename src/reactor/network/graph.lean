import reactor.basic
import digraph

namespace reactor 
namespace network

  structure graph.edge {c : ℕ} (reactors : fin c → reactor) :=
    (src : Σ r : fin c, fin (reactors r).nₒ)
    (dst : Σ r : fin c, fin (reactors r).nᵢ)

  instance {c : ℕ} {r : fin c → reactor} : digraph.edge (graph.edge r) reactor := 
    ⟨(λ e, r e.src.1), (λ e, r e.dst.1)⟩

  def graph {c : ℕ} (r : fin c → reactor) := digraph (fin c) reactor (graph.edge r)

end network
end reactor

