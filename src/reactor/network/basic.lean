import data.rel
import graphs.digraph
import reactor.basic

namespace reactor 

  namespace network

    variables {c : ℕ} (ids : finset (fin c)) (reactors : { i // i ∈ ids } → reactor)
    structure graph.edge :=
      (src : Σ r : { i // i ∈ ids }, fin (reactors r).nₒ)
      (dst : Σ r : { i // i ∈ ids }, fin (reactors r).nᵢ)

    variables {c ids reactors}
    instance graph.digraph_edge : digraph.edge (graph.edge ids reactors) (fin c) := 
      { src := (λ e, e.src.1), dst := (λ e, e.dst.1) }

  end network

  structure network (c : ℕ) :=
    (graph : digraph (fin c) reactor network.graph.edge)
    (unique : Prop)
    -- The proposition that every port in the network graph an in-degree of ≤ 1.
    -- ∀ (i₁ i₂ i ∈ g.ids) (e₁ e₂ ∈ g.edges), ⟨e₁⟩ = (i₁, i) ∧ ⟨e₂⟩ = (i₂, i) → i₁ = i₂ )

end reactor