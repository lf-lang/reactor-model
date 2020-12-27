import data.rel
import digraph
import reactor.network.basic

namespace reactor 
namespace network
namespace «precedence» 

  variables {c : ℕ} (n : network c)

  private structure reaction_index := 
    (rtr : { i // i ∈ n.φ.ids })
    (rcn : fin (n.φ.data rtr).nᵣ)

  structure graph.edge := 
    (src : reaction_index n)
    (dst : reaction_index n)

  instance graph.digraph_edge {n : network c} : digraph.edge (graph.edge n) (reaction_index n) := 
    { src := (λ e, e.src), dst := (λ e, e.dst) }

  def graph := dag (reaction_index n) reaction (λ _ _, graph.edge n)

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