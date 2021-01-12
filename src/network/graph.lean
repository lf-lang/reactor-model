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

    -- The proposition, that a network graph only contains deterministic reactors.
    def is_det (η : network.graph) : Prop :=
      ∀ r ∈ η, reactor.is_det r

    -- If a network graph is deterministic, all of its contained reactions are deterministic.
    theorem det_rcns {η : network.graph} :
      η.is_det → ∀ i : reaction.id, (η.rcn i).is_det :=
      begin
        intros h i,
        rw network.graph.rcn,
        rw network.graph.is_det at h,
        have hᵣ, from h (η.data i.rtr) ⟨i.rtr, refl _⟩,
        rw reactor.is_det at hᵣ,
        apply hᵣ,
        exact ⟨i.rcn, refl _⟩
      end

  end graph

end network