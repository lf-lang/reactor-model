import graphs.digraph
import reactor
import network.ids

namespace network

  namespace graph
    
    structure edge :=
      (src : port.id)
      (dst : port.id)

    instance digraph_edge : digraph.edge graph.edge reactor.id := 
      { src := (λ e, e.src.rtr), dst := (λ e, e.dst.rtr) }

    -- The proposition, that for all input ports (`i`) in `g` the number of edges that have `i` as
    -- destination must be ≤ 1.
    def has_unique_port_ins (g : digraph reactor.id reactor graph.edge) : Prop :=
      ∀ i, (g.edges.filter (λ e', graph.edge.dst e' = i)).card ≤ 1

  end graph

  def graph := digraph reactor.id reactor graph.edge

end network