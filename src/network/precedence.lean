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

    private def port_depends_on_reaction (p : port.id) (r : reaction.id) (η : network.graph) : Prop :=
      p.rtr = r.rtr ∧ p.prt ∈ ((η.data r.rtr).reactions r.rcn).dₒ 

    notation r-n->p := port_depends_on_reaction p r n

    private def reaction_depends_on_port (r : reaction.id) (p : port.id) (η : network.graph) : Prop :=
      p.rtr = r.rtr ∧ p.prt ∈ ((η.data r.rtr).reactions r.rcn).dᵢ

    notation p-n->r := reaction_depends_on_port r p n

    private def internally_dependent (r r' : reaction.id) : Prop :=
      r.rtr = r'.rtr ∧ r.rcn > r'.rcn

    private def externally_dependent (r r' : reaction.id) (η : network.graph) : Prop :=
      ∃ (o) (i), (r-η->o) ∧ (i-η->r') ∧ {network.graph.edge . src := o, dst := i} ∈ η.edges

    -- For all reactions that are implicitly connected in a certain way in the network,
    -- they need to have the analogous explicit connections in the precedence graph.
    def is_well_formed_over (ρ : precedence.graph) (η : network.graph) : Prop :=
      ∀ i i' ∈ ρ.ids,
        {edge . src := i, dst := i'} ∈ ρ.edges ↔ 
        (internally_dependent i i' ∨ externally_dependent i i' η)
      
  end graph

end «precedence»
end network

-- The proposition, that every well-formed precedence graph over a network is acyclic.
def network.graph.is_prec_acyclic (η : network.graph) : Prop :=
  ∀ ρ : network.precedence.graph, ρ.is_well_formed_over η → ρ.is_acyclic

namespace network
namespace «precedence» 

  theorem all_wf_prec_graphs_are_same (η : network.graph) (ρ ρ' : precedence.graph) :
    ρ.is_well_formed_over η ∧ ρ'.is_well_formed_over η → ρ = ρ' :=
    begin
      sorry
    end

  theorem any_acyc_net_graph_has_wf_prec_graph (η : network.graph) (h : η.is_acyclic) :
    ∃ ρ : precedence.graph, ρ.is_well_formed_over η :=
    sorry

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
              sorry -- apply all_wf_prec_graphs_are_same m ρ hₘ hₚ,
            }
        }
    end

end «precedence»
end network