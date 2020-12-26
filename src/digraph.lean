import data.finset  
  
class digraph.edge {idx α : Type*} (nodes : idx → α) (ε : Type*) :=
  (src : α)
  (dst : α)

structure digraph {idx α : Type*} (nodes : idx → α) (ε : Type*) [digraph.edge nodes ε] :=
  (edges : finset ε)

namespace digraph

  def has_edge_from_to {idx α ε : Type*} {nodes : idx → α} [digraph.edge nodes ε] (g : digraph nodes ε) (a a' : α) : Prop :=
    ∃ (e : ε) [e' : digraph.edge nodes ε], e'.src = a ∧ e'.dst = a' ∧ e ∈ g.edges

  notation a -g-> a' := g.has_edge_from_to a a'

  inductive path {idx α ε : Type*} {nodes : idx → α} [digraph.edge nodes ε] (g : digraph nodes ε) : α → α → Prop
    | direct {a a' : α} (h : a -g-> a') : path a a'
    | composite {a aₘ a' : α} (p : path a aₘ) (p' : path aₘ a') : path a a'

  notation a ~g~> a' := path g a a'

  def is_acyclic {idx α ε : Type*} {nodes : idx → α} [digraph.edge nodes ε] (g : digraph nodes ε) : Prop :=
    ∀ a a' : α, (a ~g~> a') → a ≠ a'

end digraph