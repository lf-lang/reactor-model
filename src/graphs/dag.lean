import graphs.digraph

variables (ι δ : Type*) (ε : Π is : finset ι, ({ i // i ∈ is } → δ) → Type*)
variables [decidable_eq ι] [∀ i d, digraph.edge (ε i d) ι]

-- A directed acyclic graph, aka DAG. 
def dag := { d : digraph ι δ ε // d.is_acyclic }

variables {ι δ ε}

def list.is_topological_order_of (l : list ι) (g : dag ι δ ε)  : Prop :=
  ∀ i i' ∈ l, (i-g.val->i') → (l.index_of i < l.index_of i')

namespace dag 

  def removing (g : dag ι δ ε) (i : ι) : dag ι δ ε :=
    let g' := g.val.removing i in
    let acyclic' : g'.is_acyclic := sorry in
    { val := g', property := acyclic' }

  -- If a DAG is non-empty, it must contain a source vertex.
  def source_vertex (g : dag ι δ ε) (_ : g.val.ids.nonempty) : ι :=
    sorry

  theorem src_vert_deg_0 (g : dag ι δ ε) (h : g.val.ids.nonempty) :
    (digraph.in_degree (source_vertex g h) g.val) = 0 :=
    sorry

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