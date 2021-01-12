import digraph
import reactor
import network.ids

namespace network

  namespace graph
    
    structure edge :=
      (src : port.id)
      (dst : port.id)

    instance digraph_edge : digraph.edge graph.edge reactor.id := 
      { src := (λ e, e.src.rtr), dst := (λ e, e.dst.rtr) }

  end graph

  def graph := digraph reactor.id reactor graph.edge

  namespace graph

    instance mem : has_mem reactor graph := {mem := λ d g, ∃ i, g.data i = d}

    -- The reactor contained in a network graph, that is associated with a given reaction ID.
    noncomputable def rtr (η : network.graph) (i : reaction.id) : reactor :=
      η.data i.rtr

    -- The reaction contained in a network graph, that is associated with a given reaction ID.
    noncomputable def rcn (η : network.graph) (i : reaction.id) : reaction :=
      (η.data i.rtr).reactions i.rcn

    -- The proposition, that for all input ports (`i`) in `η` the number of edges that have `i` as
    -- destination is ≤ 1.
    def has_unique_port_ins (η : network.graph) : Prop :=
      ∀ i, (η.edges.filter (λ e', graph.edge.dst e' = i)).card ≤ 1

    instance edge.has_le : has_le edge := ⟨λ l r, if l.src = r.src then l.dst ≤ r.dst else l.dst ≤ r.dst⟩
    instance edge.is_trans : is_trans edge has_le.le := sorry
    instance edge.is_antisymm : is_antisymm edge has_le.le := sorry
    instance edge.is_total : is_total edge has_le.le := sorry

  end graph

end network