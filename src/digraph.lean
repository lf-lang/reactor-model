import data.finset  

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Understanding.20Type.20Classes

-- Type `ε` is a `digraph.edge`-type over `α`, if any instance of it can produce a `src` and `dst` element of type `α`.
class digraph.edge (ε α : Type*) :=
  (src : ε → α)
  (dst : ε → α)

structure digraph (ι α : Type*) (ε : (ι → α) → Type*) [∀ n, digraph.edge (ε n) α] :=
  (nodes : ι → α)
  (edges : finset (ε nodes))

variables {ι α : Type*} {ε : (ι → α) → Type*} [∀ n, digraph.edge (ε n) α]

namespace digraph

  def has_edge_from_to (g : digraph ι α ε) (a a' : α) : Prop :=
    ∃ e ∈ g.edges, digraph.edge.src e = a ∧ digraph.edge.dst e = a'

  notation a-g->a' := g.has_edge_from_to a a'

  inductive has_path_from_to (g : digraph ι α ε) : α → α → Prop
    | direct {a a' : α} : (a-g->a') → has_path_from_to a a'
    | composite {a aₘ a' : α} : has_path_from_to a aₘ → has_path_from_to aₘ a' → has_path_from_to a a'

  notation a~g~>a' := g.has_path_from_to a a'

  def is_acyclic (g : digraph ι α ε) : Prop :=
    ∀ a a' : α, (a~g~>a') → a ≠ a'

  def is_input_unique (g : digraph ι α ε) : Prop :=
    ∀ (i₁ i₂ i : ι) (e₁ e₂ ∈ g.edges),
      (digraph.edge.src e₁ = g.nodes i₁) ∧ (digraph.edge.src e₂ = g.nodes i₂) →
      (digraph.edge.dst e₁ = g.nodes i ) ∧ (digraph.edge.dst e₂ = g.nodes i ) →
      i₁ = i₂ 

end digraph 

variable [decidable_eq α]
   
def list.is_topological_order_of (l : list α) (g : digraph ι α ε)  : Prop :=
  ∀ a a' ∈ l, (a-g->a') → (l.index_of a < l.index_of a')
  
namespace digraph

  def topological_sort (g : digraph ι α ε) : list α := sorry

  protected theorem topological_sort_correctness (g : digraph ι α ε) :
    (topological_sort g).is_topological_order_of g :=
    sorry

end digraph