import reactor.basic
import digraph

namespace reactor 
namespace network

  structure graph.edge {c : ℕ} (reactors : fin c → reactor) :=
    (src : Σ r : fin c, fin (reactors r).nₒ)
    (dst : Σ r : fin c, fin (reactors r).nᵢ)

  instance {c : ℕ} {rs : fin c → reactor} (g : graph.edge rs) : digraph.edge rs := 
    ⟨rs g.src.1, rs g.dst.1⟩

  def graph {c : ℕ} (reactors : fin c → reactor) := digraph reactors (graph.edge reactors)

  namespace graph

    /-inductive path {c : ℕ} (g : graph c) : fin c → fin c → Prop
      | direct {r r' : fin c} (h : has_edge_from_to g r r') : path r r'
      | composite {r rₘ r' : fin c} (p : path r rₘ) (p' : path rₘ r') : path r r'

    def is_acyclic {c : ℕ} (g : graph c) : Prop :=
      ∀ r r' : fin c, path g r r' → r ≠ r'
    -/

    def lt_le_trans {a b c : ℕ} (lt : a < b) (le : b ≤ c) : a < c := sorry

    /-def is_input_unique {c : ℕ} (g : graph c) : Prop :=
      ∀ (r₁ r₂ r : fin c) 
        (h : (g.reactors r₂).nₒ ≤ (g.reactors r₁).nₒ) -- Used only for type casting below.
        (s₁ : fin (g.reactors r₁).nₒ)
        (s₂ : fin (g.reactors r₂).nₒ)
        (d  : fin (g.reactors r).nᵢ),
          let s₂' : fin (g.reactors r₁).nₒ := ⟨s₂, lt_le_trans s₂.property h⟩ in
          ((⟨r₁, s₁, r, d⟩ : graph.edge g.reactors) ∈ g.connections ∧
          (⟨r₂, s₂, r, d⟩ : graph.edge g.reactors) ∈ g.connections)
          → (r₁, s₁) = (r₂, s₂')-/

  end graph

end network
end reactor