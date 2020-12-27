import data.finset  

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Understanding.20Type.20Classes

namespace digraph

  -- Type `ε` is a `digraph.edge`-type over `α`, if any instance of it can produce a `src` and `dst` element of type `α`.
  class edge (ε α : Type*) :=
    (src : ε → α)
    (dst : ε → α)

  namespace edge 

    def src_of {ε α : Type*} [digraph.edge ε α] (e : ε) : α := digraph.edge.src e
    def dst_of {ε α : Type*} [digraph.edge ε α] (e : ε) : α := digraph.edge.dst e

  end edge

end digraph

-- The vertices (of type `α`) have to have an associated index (of type `ι`), because otherwise it
-- wouldn't be possible to have multiple instances of the same reactor in a network.
-- Multisets are not enough, because then their edges can't be distinguished from one another.
--! The problem now is, that it is not easily possible to remove and edge from the graph, because
--! this has to coincide with the reduction of the possible indices `ι`. Perhaps this can be
--! achieved by using a subtype as the resulting index type, like:
--! `ι' = { i : ι // i != index_of_removed_vertex }`.
structure digraph (ι α : Type*) (ε : (ι → α) → Type*) [∀ n, digraph.edge (ε n) α] [fintype ι] [decidable_eq α] :=
  (nodes : ι → α)
  (edges : finset (ε nodes))

variables {ι α : Type*} {ε : (ι → α) → Type*}
variables [∀ n, digraph.edge (ε n) α] [fintype ι] [decidable_eq α]

namespace digraph

  open edge

  -- The values of the nodes contained in digraph `g`.
  def vertices (g : digraph ι α ε) : finset α :=
    finset.image g.nodes finset.univ

  -- The proposition that a given digraph connects two given vertices with an edge.
  def has_edge_from_to (g : digraph ι α ε) (v v' : α) : Prop :=
    ∃ e ∈ g.edges, (src_of e = v) ∧ (dst_of e = v')

  notation v-g->v' := g.has_edge_from_to v v'

  -- The proposition that a given digraph connects two given vertices by some path.
  inductive has_path_from_to (g : digraph ι α ε) : α → α → Prop
    | direct {v v' : α} : (v-g->v') → has_path_from_to v v'
    | composite {v vₘ v' : α} : has_path_from_to v vₘ → has_path_from_to vₘ v' → has_path_from_to v v'

  notation a~g~>a' := g.has_path_from_to a a'

  -- The proposition that a given digraph is acyclic.
  def is_acyclic (g : digraph ι α ε) : Prop :=
    ∀ a a' : α, (a~g~>a') → a ≠ a'

  -- The proposition that every node in a given digraph has an in-degree of ≤ 1.
  def is_input_unique (g : digraph ι α ε) : Prop :=
    ∀ (i₁ i₂ i : ι) (e₁ e₂ ∈ g.edges),
      (src_of e₁ = g.nodes i₁) ∧ (src_of e₂ = g.nodes i₂) →
      (dst_of e₁ = g.nodes i ) ∧ (dst_of e₂ = g.nodes i ) →
      i₁ = i₂ 

  -- The proposition that `a` is a node of in-degree 0 in `g`.
  def has_source_node (g : digraph ι α ε) (a : α) : Prop :=
    a ∈ g.vertices ∧ ∀ e ∈ g.edges, dst_of e ≠ a

  -- If a digraph is acyclic, it must contain a source node.
  theorem acyclic_has_source (g : digraph ι α ε) :
    g.is_acyclic → (∃ a : α, g.has_source_node a) :=
    begin
      intro h,
      --? rw has_source_node,
      sorry
    end

end digraph 

variable [decidable_eq α]

-- A directed acyclic graph, aka DAG. 
def dag (ι α : Type*) (ε : (ι → α) → Type*) [∀ n, digraph.edge (ε n) α] [fintype ι] [decidable_eq α] := 
  { d : digraph ι α ε // d.is_acyclic }

def list.is_topological_order_of (l : list α) (g : dag ι α ε)  : Prop :=
  ∀ a a' ∈ l, (a-(g.val)->a') → (l.index_of a < l.index_of a')

namespace digraph

  private def topological_sort' (g : dag ι α ε) (l : list (ι × α)) : (dag ι α ε) × list (ι × α) :=
    sorry

  def topological_sort (g : dag ι α ε) : list α := sorry

  protected theorem topological_sort_correctness (g : dag ι α ε) :
    (topological_sort g).is_topological_order_of g :=
    sorry

end digraph