import digraph
import network.graph
import network.ids

namespace network
namespace «precedence» 

  namespace graph

    structure edge := 
      (src : reaction.id)
      (dst : reaction.id)

    instance digraph_edge : digraph.edge graph.edge reaction.id := 
      { src := (λ e, e.src), dst := (λ e, e.dst) }

  end graph

  def graph := digraph reaction.id reaction precedence.graph.edge

  instance : has_mem reaction precedence.graph := {mem := λ r g, ∃ i, g.data i = r}

  namespace graph

    -- The reaction contained in a precedence graph, that is associated with a given reaction ID.
    noncomputable def rcn (ρ : precedence.graph) (i : reaction.id) : reaction :=
      ρ.data i

    private def port_depends_on_reaction (p : port.id) (r : reaction.id) (η : network.graph) : Prop :=
      p.rtr = r.rtr ∧ p.prt ∈ ((η.data r.rtr).reactions r.rcn).dₒ 

    notation r-n->p := port_depends_on_reaction p r n

    private def reaction_depends_on_port (r : reaction.id) (p : port.id) (η : network.graph) : Prop :=
      p.rtr = r.rtr ∧ p.prt ∈ ((η.data r.rtr).reactions r.rcn).dᵢ

    notation p-n->r := reaction_depends_on_port r p n

    -- A reaction `r` is internally dependent on `r'` if they live in the same reactor and `r`'s
    -- priority is above `r'`'s.
    --
    -- Note, this implies that reactions can have multiple internal dependencies, and hence a
    -- well-formed precedence graph will have an edge for each of these. This doesn't matter
    -- though, because the topological order is not affected by this.
    private def internally_dependent (r r' : reaction.id) : Prop :=
      r.rtr = r'.rtr ∧ r.rcn > r'.rcn

    -- A reaction `r` is externally dependent on `r'` there is a connection from an output-port of
    -- `r` to an input-port of `r'`.
    private def externally_dependent (r r' : reaction.id) (η : network.graph) : Prop :=
      ∃ (o) (i), (r-η->o) ∧ {network.graph.edge . src := o, dst := i} ∈ η.edges ∧ (i-η->r')

    -- A well-formed precedence graph should contain edges between exactly those reactions that
    -- have a direct dependency in the corresponding network graph.
    def edges_are_well_formed_over (ρ : precedence.graph) (η : network.graph) : Prop :=
      ∀ i i' ∈ ρ.ids,
        {edge . src := i, dst := i'} ∈ ρ.edges ↔ 
        (internally_dependent i i' ∨ externally_dependent i i' η)

    -- A well-formed precedence graph should contain an ID (and by extension a member) iff
    -- the ID can be used to identify a reaction in the corresponding network graph.
    def ids_are_well_formed_over (ρ : precedence.graph) (η : network.graph) : Prop :=
      ∀ i : reaction.id, i ∈ ρ.ids ↔ (i.rtr ∈ η.ids ∧ i.rcn ∈ (η.rtr i).priorities)
      
    -- A well-formed precedence graph's data map should return exactly those reactions that
    -- correspond to the given ID in the network graph.
    def data_is_well_formed_over (ρ : precedence.graph) (η : network.graph) : Prop :=
      ∀ i ∈ ρ.ids, ρ.rcn i = η.rcn i

    def is_well_formed_over (ρ : precedence.graph) (η : network.graph) : Prop :=
      ρ.edges_are_well_formed_over η ∧
      ρ.ids_are_well_formed_over   η ∧ 
      ρ.data_is_well_formed_over   η 

  end graph

end «precedence»
end network

-- The proposition, that every well-formed precedence graph over a network is acyclic.
def network.graph.is_prec_acyclic (η : network.graph) : Prop :=
  ∀ ρ : network.precedence.graph, ρ.is_well_formed_over η → ρ.is_acyclic

namespace network
namespace «precedence»

  theorem any_acyc_net_graph_has_wf_prec_graph (η : network.graph) (h : η.is_acyclic) :
    ∃ ρ : precedence.graph, ρ.is_well_formed_over η :=
    sorry

  theorem all_wf_prec_graphs_are_same (η : network.graph) (ρ ρ' : precedence.graph) :
    ρ.is_well_formed_over η ∧ ρ'.is_well_formed_over η → ρ = ρ' :=
    begin
      sorry
    end

  theorem any_acyc_net_graph_has_exactly_one_wf_prec_graph (η : network.graph) (h : η.is_acyclic) :
    ∃! ρ : precedence.graph, ρ.is_well_formed_over η :=
    begin
      rw exists_unique,
      let ρ := (any_acyc_net_graph_has_wf_prec_graph η h).some,
      have hₚ, from (any_acyc_net_graph_has_wf_prec_graph η h).some_spec,
      apply exists.intro,
        {
          apply and.intro,
            exact hₚ,
            {
              intros m hₘ,
              apply all_wf_prec_graphs_are_same η m ρ ⟨hₘ, hₚ⟩
            }
        }
    end

end «precedence»
end network