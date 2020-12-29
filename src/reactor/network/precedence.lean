import data.rel
import graphs.digraph
import reactor.network.basic

namespace reactor 
namespace network
namespace «precedence» 

  variables {c : ℕ} (n : network c)

  namespace graph

    structure reaction_id := 
      (rtr : { i // i ∈ n.graph.ids })
      (rcn : fin (n.graph.data rtr).nᵣ)

    instance dec_eq_rcn_id : decidable_eq (reaction_id n) := sorry

    structure edge := 
      (src : reaction_id n)
      (dst : reaction_id n)

    instance digraph_edge {n : network c} : digraph.edge (graph.edge n) (reaction_id n) := 
      { src := (λ e, e.src), dst := (λ e, e.dst) }

  end graph

  def graph := digraph (graph.reaction_id n) reaction (λ _ _, graph.edge n)

  namespace graph

    def is_well_formed {n : network c} (g : precedence.graph n) : Prop :=
      true
      -- For all reactions that are implicitly connected in a certain way in the network,
      -- they need to have the analogous explicit connections in the precedence graph.

    def «from» (n : network c) : precedence.graph n := sorry

    theorem from_network_correctness (n : network c) :
      (precedence.graph.from n).is_well_formed := 
      sorry

  end graph

end «precedence»
end network
end reactor