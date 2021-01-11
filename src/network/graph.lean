import graphs.digraph
import reactor
import network.ids

namespace network

  namespace graph
    
    variables (c : ℕ)
    structure edge :=
      (src : port.id c)
      (dst : port.id c)

    variable {c}
    instance digraph_edge : digraph.edge (graph.edge c) (reactor.id c) := 
      { src := (λ e, e.src.rtr), dst := (λ e, e.dst.rtr) }

    -- The proposition, that for all input ports (`i`) in `g` the number of edges that have `i` as
    -- destination must be ≤ 1.
    def has_unique_port_ins (g : digraph (reactor.id c) reactor (graph.edge c)) : Prop :=
      ∀ i, (g.edges.filter (λ e', graph.edge.dst e' = i)).card ≤ 1

  end graph

  def graph (c : ℕ) := digraph (reactor.id c) reactor (graph.edge c)

end network