import data.rel
import graphs.digraph
import reactor.basic

namespace reactor 

  namespace network

    variables {c : ℕ} (ids : finset (fin c)) (reactors : { i // i ∈ ids } → reactor)
    structure graph.edge :=
      (src : Σ r : { i // i ∈ ids }, fin (reactors r).nₒ)
      (dst : Σ r : { i // i ∈ ids }, fin (reactors r).nᵢ)

    variables {c ids reactors}
    instance graph.digraph_edge : digraph.edge (graph.edge ids reactors) (fin c) := 
      { src := (λ e, e.src.1), dst := (λ e, e.dst.1) }

    -- The proposition, that for all input ports (`i`) in `g` the number of edges that have `i` as
    -- destination must be ≤ 1.
    def graph.port_unique_ins (g : digraph (fin c) reactor network.graph.edge) : Prop :=
      ∀ i : Σ r : { x // x ∈ g.ids }, fin (g.data r).nᵢ,
        (g.edges.filter (λ e', graph.edge.dst e' = i)).card ≤ 1

  end network

  structure network (c : ℕ) :=
    (graph : digraph (fin c) reactor network.graph.edge)
    (unique_ins : network.graph.port_unique_ins graph)
    
end reactor