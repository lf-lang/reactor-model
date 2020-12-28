import data.rel
import graphs.dag
import reactor.basic

open classical

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
  
  --! The `nodes` should really be part of `φ`. 
  --! This is currently not possible, because the network.graph needs to
  --! know the type of it's nodes in order to know the type of its edges.
  --! -> digraph needs to be adjusted to solve this
  structure network (c : ℕ) :=
    (graph : dag (fin c) reactor network.graph.edge)
    (unique : Prop)
    -- The proposition that every port in the network graph an in-degree of ≤ 1.
    -- ∀ (i₁ i₂ i ∈ g.ids) (e₁ e₂ ∈ g.edges), ⟨e₁⟩ = (i₁, i) ∧ ⟨e₂⟩ = (i₂, i) → i₁ = i₂ )

  namespace network

    private def run' {c : ℕ} (n : network c) (topo : list (fin c)) : (network c) × list (fin c) := sorry
    def run {c : ℕ} (n : network c) : network c := sorry

    -- reactor.network.process should use the fixed-point approach from *dataflow with firing*.
    -- reaching a fixed point is equivalent to the global reaction-queue being computed until it is empty
    -- (which would then induce the next time-stamp to be run. without actions a reactor system will only have
    -- one time stamp (because there are no actions to increase them), so the fixed point is a static final state?)

    -- order.basic contains a definition of `monotone`
    -- order.directed contains a definition of `directed`

  end network

end reactor