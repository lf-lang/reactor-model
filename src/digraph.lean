import data.finset  

-- digraph.edge is a property over ε that states that it has a src and dst of type α
class digraph.edge (ε α : Type*) :=
  (src : ε → α)
  (dst : ε → α)

structure digraph (ι α ε : Type*) [digraph.edge ε α] :=
  (nodes : ι → α)
  (edges : finset ε)

namespace digraph

  def has_edge_from_to {ι α ε : Type*} [ε' : digraph.edge ε α] (g : digraph ι α ε) (a a' : α) : Prop :=
    ∃ e ∈ g.edges, (ε'.src e) = a ∧ (ε'.dst e) = a'

  notation a -g-> a' := g.has_edge_from_to a a'

  inductive has_path_from_to {ι α ε : Type*} [digraph.edge ε α] (g : digraph ι α ε) : α → α → Prop
    | direct {a a' : α} (h : a -g-> a') : has_path_from_to a a'
    | composite {a aₘ a' : α} (p : has_path_from_to a aₘ) (p' : has_path_from_to aₘ a') : has_path_from_to a a'

  notation a ~g~> a' := has_path_from_to g a a'

  def is_acyclic {ι α ε : Type*} [digraph.edge ε α] (g : digraph ι α ε) : Prop :=
    ∀ a a' : α, (a ~g~> a') → a ≠ a'

  def is_input_unique {ι α ε : Type*} [ε' : digraph.edge ε α] (g : digraph ι α ε) : Prop :=
    ∀ (i₁ i₂ i : ι) (e₁ e₂ ∈ g.edges),
      (ε'.src e₁ = g.nodes i₁) ∧ (ε'.src e₂ = g.nodes i₂) →
      (ε'.dst e₁ = g.nodes i ) ∧ (ε'.dst e₂ = g.nodes i ) →
      i₁ = i₂ 
      
end digraph