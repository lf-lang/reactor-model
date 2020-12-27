import data.rel
import digraph
import reactor.network.basic

namespace reactor 
namespace network
namespace «precedence» 

  variable  {c : ℕ}

  private structure reaction_index (n : network c) := 
    (rtr : fin c)
    (rcn : fin (n.φ.nodes rtr).nᵣ)
  
  structure graph.edge {n : network c} (_ : reaction_index n → reaction) := 
    (src : reaction_index n)
    (dst : reaction_index n)

  instance prec_graph_edge {n : network c} {r : reaction_index n → reaction} : digraph.edge (graph.edge r) reaction := 
    {
      src := (λ e, r e.src), 
      dst := (λ e, r e.dst)
    }

  def graph (n : network c) := digraph (reaction_index n) reaction graph.edge

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