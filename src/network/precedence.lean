import graphs.digraph
import network.graph
import network.ids

namespace network
namespace «precedence» 

  variables {c : ℕ} (ρ : reactor.id c → reactor)

  namespace graph

    structure edge := 
      (src : reaction.id ρ)
      (dst : reaction.id ρ)

    variable {ρ}
    instance digraph_edge : digraph.edge (graph.edge ρ) (reaction.id ρ) := 
      { src := (λ e, e.src), dst := (λ e, e.dst) }

  end graph

  variable (n : network.graph c)
  def graph := digraph (reaction.id n.data) reaction (graph.edge n.data)

  variable {n}
  instance : has_mem reaction (graph n) := {mem := λ r g, ∃ i, g.data i = r}

  namespace graph

    private def internally_dependent (r r' : reaction.id n.data) (g : precedence.graph n) : Prop :=
      --! The `val` could be removed here by proving that `(n.data r'.rtr).nᵣ = (n.data r.rtr).nᵣ`.
      r.rtr = r'.rtr ∧ r.rcn.val < r'.rcn.val

    private def externally_dependent (r r' : reaction.id n.data) (g : precedence.graph n) : Prop :=
      ∃ o, port_depends_on_reaction o r → 
      ∃ i, reaction_depends_on_port r' i → 
        {network.graph.edge . src := o, dst := i} ∈ n.edges

    -- For all reactions that are implicitly connected in a certain way in the network,
    -- they need to have the analogous explicit connections in the precedence graph.
    def is_well_formed (g : precedence.graph n) : Prop :=
      ∀ i i' ∈ g.ids,
        (internally_dependent i i' g ∨ externally_dependent i i' g) ↔ 
        {edge . src := i, dst := i'} ∈ g.edges
      
  end graph

  theorem all_wf_prec_graphs_are_same {n : network.graph c} (p p' : precedence.graph n):
      p.is_well_formed → p'.is_well_formed → p = p' :=
      begin
        sorry
      end

    theorem any_acyc_net_graph_has_wf_prec_graph (n : network.graph c) (h : n.is_acyclic) :
      ∃ p : precedence.graph n, p.is_well_formed :=
      sorry

    theorem any_acyc_net_graph_has_exactly_one_wf_prec_graph (n : network.graph c) (h : n.is_acyclic) :
      ∃! p : precedence.graph n, p.is_well_formed :=
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
                apply all_wf_prec_graphs_are_same m p hₘ hₚ,
              }
          }
      end

      theorem exis_ndet_prec_func (c : ℕ) :
        ∃ f : (network.graph c) ~?> (λ n, precedence.graph n), ∀ n p, p ∈ (f n) → graph.is_well_formed p :=
        sorry

end «precedence»
end network