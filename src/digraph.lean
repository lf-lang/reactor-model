import data.finset  

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Understanding.20Type.20Classes

namespace digraph

  -- Type `ε` is a `digraph.edge`-type over indices `ι`, if any instance of it can produce a `src`
  -- and `dst` index.
  class edge (ε ι : Type*) :=
    (src : ε → ι)
    (dst : ε → ι)

  notation ⟨e⟩ := (digraph.edge.src e, digraph.edge.dst e)

end digraph

variables (ι δ : Type*) (ε : Π is : finset ι, ({ i // i ∈ is } → δ) → Type*)
variables [∀ i d, digraph.edge (ε i d) ι]

-- The vertices (of type `α`) have to have an associated index (of type `ι`), because otherwise it
-- wouldn't be possible to have multiple instances of the same reactor in a network.
-- Multisets are not enough, because then their edges can't be distinguished from one another.
--! The problem now is, that it is not easily possible to remove and edge from the graph, because
--! this has to coincide with the reduction of the possible indices `ι`. Perhaps this can be
--! achieved by using a subtype as the resulting index type, like:
--! `ι' = { i : ι // i != index_of_removed_vertex }`.
structure digraph :=
  (ids : finset ι)
  (data : { i // i ∈ ids } → δ)
  (edges : finset (ε ids data))

variables {ι δ ε}

namespace digraph

  open edge

  -- The proposition that a given digraph connects two given vertices with an edge.
  def has_edge_from_to (g : digraph ι δ ε) (i i' : ι) : Prop :=
    ∃ e ∈ g.edges, ⟨e⟩ = (i, i')

  notation i-g->i' := g.has_edge_from_to i i'

  -- The proposition that a given digraph connects two given vertices by some path.
  inductive has_path_from_to (g : digraph ι δ ε) : ι → ι → Prop
    | direct {i i' : ι} : (i-g->i') → has_path_from_to i i'
    | composite {i iₘ i' : ι} : has_path_from_to i iₘ → has_path_from_to iₘ i' → has_path_from_to i i'

  notation i~g~>i' := g.has_path_from_to i i'

  -- The proposition that a given digraph is acyclic.
  def is_acyclic (g : digraph ι δ ε) : Prop :=
    ∀ i i' : ι, (i~g~>i') → i ≠ i'

  -- The proposition that every node in a given digraph has an in-degree of ≤ 1.
  def is_input_unique (g : digraph ι δ ε) : Prop :=
    ∀ (i₁ i₂ i ∈ g.ids) (e₁ e₂ ∈ g.edges), 
      ⟨e₁⟩ = (i₁, i) ∧ ⟨e₂⟩ = (i₂, i) → i₁ = i₂ 
      
  -- The proposition that `i` is a vertex of in-degree 0 in `g`.
  def has_source_node (g : digraph ι δ ε) (i : ι) : Prop :=
    i ∈ g.ids ∧ ∀ e ∈ g.edges, (digraph.edge.dst e) ≠ i

  -- If a digraph is acyclic, it must contain a source node.
  theorem acyclic_has_source (g : digraph ι δ ε) :
    g.is_acyclic → (∃ i : ι, g.has_source_node i) :=
    begin
      intro h,
      --? rw has_source_node,
      sorry
    end

end digraph 

variables (ι δ ε)

-- A directed acyclic graph, aka DAG. 
def dag := { d : digraph ι δ ε // d.is_acyclic }

variables {ι δ ε} [decidable_eq ι]

def list.is_topological_order_of (l : list ι) (g : dag ι δ ε)  : Prop :=
  ∀ i i' ∈ l, (i-g.val->i') → (l.index_of i < l.index_of i')

namespace digraph

  private def topological_sort' (g : dag ι δ ε) (acc : list ι) : (dag ι δ ε) × list ι :=
    -- The return type should work as `dag ι δ ε` now.
    sorry

  def topological_sort (g : dag ι δ ε) : list ι := sorry

  protected theorem topological_sort_correctness (g : dag ι δ ε) :
    (topological_sort g).is_topological_order_of g :=
    sorry

end digraph