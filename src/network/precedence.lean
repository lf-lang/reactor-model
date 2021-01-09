import graphs.digraph
import network.graph

namespace network
namespace «precedence» 

  variables {c : ℕ} (n : network.graph c)

  namespace graph

    structure reaction_id := 
      (rtr : { i // i ∈ n.ids })
      (rcn : fin (n.data rtr).nᵣ)

    instance dec_eq_rcn_id : decidable_eq (reaction_id n) := sorry

    structure edge := 
      (src : reaction_id n)
      (dst : reaction_id n)

    variable {n}
    instance digraph_edge : digraph.edge (graph.edge n) (reaction_id n) := 
      { src := (λ e, e.src), dst := (λ e, e.dst) }

  end graph

  def graph := digraph (graph.reaction_id n) reaction (λ _ _, graph.edge n)

  instance : has_mem reaction (graph n) := {mem := λ r g, ∃ i, g.data i = r}

  namespace graph

    variable {n}

    def is_internally_well_formed (g : precedence.graph n) : Prop :=
      ∀ i i' ∈ g.ids,
        (reaction_id.rtr i = (reaction_id.rtr i') → 
        i.rcn.val < i'.rcn.val → 
        {edge . src := i, dst := i'} ∈ g.edges

    def is_externally_well_formed (g : precedence.graph n) : Prop :=
      ∀ i i', (subtype.val i) ∈ g.ids → (subtype.val i') ∈ g.ids →
      ∃ i_ad, i_ad ∈ (g.data i).dₒ → 
      ∃ i'_d, i'_d ∈ (g.data i').dᵢ → 
        let src : Σ r : { i // i ∈ n.ids }, port_id (n.data r).nₒ := ⟨i.val.rtr, sorry /-i_ad-/⟩ in
        let dst : Σ r : { i // i ∈ n.ids }, port_id (n.data r).nᵢ := ⟨i'.val.rtr, sorry /-i'_d-/⟩ in
        {network.graph.edge . src := src, dst := dst} ∈ n.edges → 
        {edge . src := i.val, dst := i'.val} ∈ g.edges

    -- For all reactions that are implicitly connected in a certain way in the network,
    -- they need to have the analogous explicit connections in the precedence graph.
    def is_well_formed (g : precedence.graph n) : Prop :=
      is_internally_well_formed g ∧ is_externally_well_formed g

    theorem any_acyc_net_graph_has_exactly_one_wf_prec_graph :
      ∀ (n : network.graph c) (h : n.is_acyclic), ∃! p : precedence.graph n, p.is_well_formed :=
      sorry
      
  end graph

end «precedence»
end network