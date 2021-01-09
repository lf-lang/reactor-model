import graphs.digraph
import reactor

namespace network

  def reactor_id (c : ℕ) := fin c
  def port_id (c : ℕ) := fin c

  namespace graph
    
    variables {c : ℕ} (ids : finset (reactor_id c)) (reactors : { i // i ∈ ids } → reactor)
    structure edge :=
      (src : Σ r : { i // i ∈ ids }, port_id (reactors r).nₒ)
      (dst : Σ r : { i // i ∈ ids }, port_id (reactors r).nᵢ)

    variables {ids reactors}
    instance digraph_edge : digraph.edge (graph.edge ids reactors) (reactor_id c) := 
      { src := (λ e, e.src.1), dst := (λ e, e.dst.1) }

    -- The proposition, that for all input ports (`i`) in `g` the number of edges that have `i` as
    -- destination must be ≤ 1.
    def has_unique_port_ins (g : digraph (reactor_id c) reactor network.graph.edge) : Prop :=
      ∀ i, (g.edges.filter (λ e', graph.edge.dst e' = i)).card ≤ 1

  end graph

  def graph (c : ℕ) := digraph (reactor_id c) reactor graph.edge

end network