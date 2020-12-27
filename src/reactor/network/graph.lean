import reactor.basic
import digraph

namespace reactor 
namespace network

  variables {c : ℕ} (ids : finset (fin c)) (reactors : { i // i ∈ ids } → reactor)
  structure graph.edge :=
    (src : Σ r : { i // i ∈ ids }, fin (reactors r).nₒ)
    (dst : Σ r : { i // i ∈ ids }, fin (reactors r).nᵢ)

  variables {c ids reactors}
  instance graph.digraph_edge : digraph.edge (graph.edge ids reactors) (fin c) := 
    { src := (λ e, e.src.1), dst := (λ e, e.dst.1) }

  --! Optimally this would be a DAG, but currently this implies that
  --! `φ.is_input_unique` doesn't work then.
  def graph (c : ℕ) := digraph (fin c) reactor graph.edge

end network
end reactor

