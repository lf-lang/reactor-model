import data.finset  

-- Associated discussion:
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Understanding.20Type.20Classes

-- Type `ε` is a `digraph.edge`-type over indices `ι`, if any instance of it can produce a `src`
-- and `dst` index.
class digraph.edge (ε ι : Type*) :=
  (src : ε → ι)
  (dst : ε → ι)

variables (ι δ ε : Type*)
variables [decidable_eq ι] [decidable_eq δ] [digraph.edge ε ι]

-- The vertices (of type `α`) have to have an associated index (of type `ι`), because otherwise it
-- wouldn't be possible to have multiple instances of the same reactor in a network.
-- Multisets are not enough, because then their edges can't be distinguished from one another.
--
-- A previous approach defined the nodes and indices together, as `ι → δ`. The nice thing about
-- this was that all indices of type `ι` were guaranteed to reference a vertex in the graph. The
-- problem with this though, is that you can't remove/add a vertex from/to the graph without
-- changing the underlying index-type `ι`. Hence the current approach which uses a `finset ι` is
-- used, so `ι` can stay the same. An inconvenience that arises as a result of this more flexible
-- approach is that functions over indices might have to require `(i : { x // x ∈ g.ids})` as
-- parameter instead of just `(i : ι)`.
@[ext] -- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/How.20to.20prove.20.20equality.20of.20structure/near/202105252
structure digraph :=
  (ids : finset ι)
  (data : ι → δ)
  (edges : finset ε)

variables {ι δ ε}

instance : has_mem δ (digraph ι δ ε) := {mem := λ d g, ∃ i, g.data i = d}

namespace digraph

  -- The data elements contained in a given digraph.
  def members (g : digraph ι δ ε) : finset δ :=
    g.ids.image g.data

  -- Produces a graph where the member at a given ID `i` is replaced by a new member `d`.
  def update_data (g : digraph ι δ ε) (i : ι) (d : δ) : digraph ι δ ε :=
    {digraph . data := (λ x : ι, if x = i then d else g.data x), ..g} 

  -- The proposition that a given digraph connects two given vertices with an edge.
  def has_edge_from_to (g : digraph ι δ ε) (i i' : ι) : Prop :=
    ∃ e ∈ g.edges, (edge.src e, edge.dst e) = (i, i')

  notation i-g->i' := g.has_edge_from_to i i'

  -- The proposition that a given digraph connects two given vertices by some path.
  inductive has_path_from_to (g : digraph ι δ ε) : ι → ι → Prop
    | direct {i i' : ι} : (i-g->i') → has_path_from_to i i'
    | composite {i iₘ i' : ι} : has_path_from_to i iₘ → has_path_from_to iₘ i' → has_path_from_to i i'

  notation i~g~>i' := g.has_path_from_to i i'

  -- The proposition that a given digraph is acyclic.
  def is_acyclic (g : digraph ι δ ε) := ∀ i, ¬ i~g~>i

  variable [decidable_eq ι]

  -- The definition of what it means for a given list to be a topological order of a given DAG.
  def topological_order (g : digraph ι δ ε) (h : g.is_acyclic) (l : list ι) : Prop :=
    ∀ i i' ∈ l, (i-g->i') → (l.index_of i < l.index_of i')

  -- For any DAG there exists a list which is a topological order of the DAG.
  theorem any_dag_has_topo : 
    ∀ (g : digraph ι δ ε) (h : g.is_acyclic), ∃ l : list ι, topological_order g h l :=
    -- https://ocw.tudelft.nl/wp-content/uploads/Algoritmiek_DAGs_and_Topological_Ordering.pdf
    -- Lemma 3.20

  -- The in-degree of vertex `i` in digraph `g`. 
  def in_degree_of (g : digraph ι δ ε) (i : { x // x ∈ g.ids}) : ℕ :=
    (g.edges.filter (λ e, edge.dst e = i.val)).card

end digraph 










