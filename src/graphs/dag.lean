import graphs.digraph
import init.algebra.classes

variables (ι δ : Type*) (ε : Π is : finset ι, ({ i // i ∈ is } → δ) → Type*)
variables [∀ i d, digraph.edge (ε i d) ι]

-- A directed acyclic graph, aka DAG. 
def dag := { d : digraph ι δ ε // d.is_acyclic } 

namespace dag 

  variables {ι δ ε} [decidable_eq ι]

  def is_topological_order_of (l : list ι) (g : dag ι δ ε) : Prop :=
    ∀ i i' ∈ l, (i-g.val->i') → (l.index_of i < l.index_of i')

  def removing (g : dag ι δ ε) (i : { x // x ∈ g.val.ids}) : dag ι δ ε :=
    let g' := g.val.removing i in
    let acyclic' : g'.is_acyclic := sorry in
    { val := g', property := acyclic' }

  section

    variable (g : dag ι δ ε) 
    variables [has_lt { i // i ∈ g.val.ids }] [@decidable_rel { i // i ∈ g.val.ids } (<)] [is_linear_order { i // i ∈ g.val.ids } (<)]

    private lemma ex_edge_no_pred : ∃ e ∈ g.val.edges, ∀ e' ∈ g.val.edges, (digraph.edge.src e : ι) ≠ (digraph.edge.dst e') :=
    begin
      by_contra,
      sorry
    end

    -- A predicate that identifies source vertices.
    private def is_source_vertex {g : dag ι δ ε} (i : { x // x ∈ g.val.ids }) : Prop := 
      g.val.in_degree_of i = 0

    private lemma has_source_vertex (h : g.val.ids.nonempty) : 
      ∃ i : { x // x ∈ g.val.ids }, is_source_vertex i :=
      begin
        intro g.property,
      end

    -- If a DAG is non-empty, it must contain a source vertex.
    def source_vertex (h : g.val.ids.nonempty) : { i // i ∈ g.val.ids } :=
      -- Flatten the vertices into a list sorted by their own order.
      let ids := g.val.ids.attach.sort (<) in
      -- Get a proof of the fact that `ids` must contain a source vertex (i.e. a vertex of in-degree 0).
      let list_contains_src_vert : ∃ i : { x // x ∈ g.val.ids }, i ∈ ids ∧ is_source_vertex i := 
      begin
        sorry
      end in
      -- Get the first vertex that has a in-degree of 0.
      ids.choose_x is_source_vertex list_contains_src_vert

    theorem src_vert_deg_0 (h : g.val.ids.nonempty) :
      (g.val.in_degree_of (g.source_vertex h)) = 0 :=
      sorry

  end

  instance {g : dag ι δ ε} : decidable g.val.ids.nonempty := sorry

  -- https://courses.cs.washington.edu/courses/cse326/03wi/lectures/RaoLect20.pdf

  private def topological_sort' (g : dag ι δ ε) (acc : list ι) : (dag ι δ ε) × list ι :=
    if h : g.val.ids.nonempty then 
      let src_vert := source_vertex g h in
      let g' := g.removing src_vert in
      (g', acc ++ [src_vert])
    else 
      (g, acc)

  def topological_sort (g : dag ι δ ε) : list ι := sorry

  protected theorem topological_sort_correctness (g : dag ι δ ε) :
    (topological_sort g).is_topological_order_of g :=
    sorry

end dag