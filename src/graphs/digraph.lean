import data.finset  

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Understanding.20Type.20Classes

namespace digraph

  -- Type `ε` is a `digraph.edge`-type over indices `ι`, if any instance of it can produce a `src`
  -- and `dst` index.
  class edge (ε ι : Type*) [decidable_eq ι] :=
    (src : ε → ι)
    (dst : ε → ι)

  notation ⟨e⟩ := (digraph.edge.src e, digraph.edge.dst e)

end digraph

variables (ι δ : Type*) (ε : Π is : finset ι, ({ i // i ∈ is } → δ) → Type*)
variables [decidable_eq ι] [∀ i d, digraph.edge (ε i d) ι]

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
      
  -- The in-degree of vertex `i` in digraph `g`.
  def in_degree (i : ι) (g : digraph ι δ ε) : ℕ :=
    (g.edges.filter (λ e, dst e = i)).card

  -- The digraph that remains after removing a given vertex (and all of its associated edges).
  def removing (g : digraph ι δ ε) (i : ι) : digraph ι δ ε :=
    let ids' := g.ids.erase i in
    let id_incl : Π x ∈ ids', x ∈ g.ids := λ x, finset.mem_of_subset (finset.erase_subset i g.ids) in
    let data' : { x // x ∈ ids' } → δ := λ i, g.data { val := i.val, property := id_incl i.val i.property } in
    let edges' := g.edges.filter (λ e, src e ≠ i ∧ dst e ≠ i) in
    { ids := ids', data := data', edges := edges'.map (sorry) } 

end digraph 










