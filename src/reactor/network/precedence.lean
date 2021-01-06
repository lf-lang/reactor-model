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

  instance : has_mem reaction (graph n) := {mem := λ r g, ∃ i, g.data i = r}

  namespace graph

    variable {n}

    def internally_correct (g : precedence.graph n) : Prop :=
      ∀ i i' ∈ g.ids,
        (reaction_id.rtr i = (reaction_id.rtr i') → 
        i.rcn.val < i'.rcn.val → 
        {edge . src := i, dst := i'} ∈ g.edges

    def externally_correct (g : precedence.graph n) : Prop :=
      ∀ i i', (subtype.val i) ∈ g.ids → (subtype.val i') ∈ g.ids →
      ∃ i_ad, i_ad ∈ (g.data i).dₒ → 
      ∃ i'_d, i'_d ∈ (g.data i').dᵢ → 
        let src : Σ r : { i // i ∈ n.graph.ids }, port_id (n.graph.data r).nₒ := ⟨i.val.rtr, sorry /-i_ad-/⟩ in
        let dst : Σ r : { i // i ∈ n.graph.ids }, port_id (n.graph.data r).nᵢ := ⟨i'.val.rtr, sorry /-i'_d-/⟩ in
        {network.graph.edge . src := src, dst := dst} ∈ n.graph.edges → 
        {edge . src := i.val, dst := i'.val} ∈ g.edges

    -- For all reactions that are implicitly connected in a certain way in the network,
    -- they need to have the analogous explicit connections in the precedence graph.
    def correct (g : precedence.graph n) : Prop :=
      internally_correct g ∧ externally_correct g

    theorem any_network_has_corr_prec :
      ∀ n : network c, ∃ p : precedence.graph n, correct p :=
      sorry
      
  end graph

end «precedence»
end network
end reactor