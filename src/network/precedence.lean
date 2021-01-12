import graphs.digraph
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

    private def port_depends_on_reaction (p : port.id) (r : reaction.id) (n : network.graph) : Prop :=
      p.rtr = r.rtr ∧ p.prt ∈ ((n.data r.rtr).reactions r.rcn).dₒ 

    notation r-n->p := port_depends_on_reaction p r n

    private def reaction_depends_on_port (r : reaction.id) (p : port.id) (n : network.graph) : Prop :=
      p.rtr = r.rtr ∧ p.prt ∈ ((n.data r.rtr).reactions r.rcn).dᵢ

    notation p-n->r := reaction_depends_on_port r p n

    private def internally_dependent (r r' : reaction.id) (n : network.graph) : Prop :=
      r.rtr = r'.rtr ∧ r.rcn > r'.rcn

    private def externally_dependent (r r' : reaction.id) (n : network.graph) : Prop :=
      ∃ (o) (i), (r-n->o) ∧ (i-n->r') ∧ {network.graph.edge . src := o, dst := i} ∈ n.edges

    -- For all reactions that are implicitly connected in a certain way in the network,
    -- they need to have the analogous explicit connections in the precedence graph.
    def is_well_formed_over (p : precedence.graph) (n : network.graph) : Prop :=
      ∀ i i' ∈ p.ids,
        {edge . src := i, dst := i'} ∈ p.edges ↔ 
        (internally_dependent i i' n ∨ externally_dependent i i' n)
      
  end graph

  theorem all_wf_prec_graphs_are_same (n : network.graph) (p p' : precedence.graph):
      p.is_well_formed_over n ∧ p'.is_well_formed_over n → p = p' :=
      begin
        sorry
      end

    theorem any_acyc_net_graph_has_wf_prec_graph (n : network.graph) (h : n.is_acyclic) :
      ∃ p : precedence.graph, p.is_well_formed_over n :=
      sorry

    theorem any_acyc_net_graph_has_exactly_one_wf_prec_graph (n : network.graph) (h : n.is_acyclic) :
      ∃! p : precedence.graph, p.is_well_formed_over n :=
      begin
        rw exists_unique,
        let p := (any_acyc_net_graph_has_wf_prec_graph n h).some,
        have hₚ, from (any_acyc_net_graph_has_wf_prec_graph n h).some_spec,
        apply exists.intro,
          {
            apply and.intro,
              exact hₚ,
              {
                intros m hₘ,
                sorry -- apply all_wf_prec_graphs_are_same m p hₘ hₚ,
              }
          }
      end

end «precedence»
end network