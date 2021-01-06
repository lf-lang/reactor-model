import graphs.digraph

variables (ι δ : Type*) (ε : Π is : finset ι, ({ i // i ∈ is } → δ) → Type*)
variables [∀ i d, digraph.edge (ε i d) ι]

-- A directed acyclic graph, aka DAG. 
def dag := { d : digraph ι δ ε // d.is_acyclic } 

namespace dag 

  variables {ι δ ε} [decidable_eq ι]

  def removing (g : dag ι δ ε) (i : { x // x ∈ g.val.ids}) : dag ι δ ε :=
    let g' := g.val.removing i in
    let acyclic' : g'.is_acyclic := sorry in
    { val := g', property := acyclic' }

  def source_vertex (g : dag ι δ ε) (i : ι) (h : i ∈ g.val.ids) : Prop :=
    g.val.in_degree_of ⟨i, h⟩ = 0

  -- If a DAG is non-empty, it must contain a source vertex.
  theorem has_source_vertex (g : dag ι δ ε) (h : g.val.ids.nonempty) : 
    ∃ (i : ι) (h : i ∈ g.val.ids), source_vertex g i h :=
    sorry

  instance {g : dag ι δ ε} : decidable g.val.ids.nonempty := sorry

  -- https://courses.cs.washington.edu/courses/cse326/03wi/lectures/RaoLect20.pdf

  private def topological_sort' (g : dag ι δ ε) (acc : list ι) : (dag ι δ ε) × list ι :=
    if h : g.val.ids.nonempty then 
      let src_vert : { x // x ∈ g.val.ids } := sorry in
      let g' := g.removing src_vert in
      (g', acc ++ [src_vert])
    else 
      (g, acc)

  def topological_sort (g : dag ι δ ε) : list ι :=
    (topological_sort' g []).2

  def has_topological_order (g : dag ι δ ε) (l : list ι) : Prop :=
    ∀ i i' ∈ l, (i-g.val->i') → (l.index_of i < l.index_of i')

  -- Execution of the reactor network needs to be the same no matter which concrete topo-list it gets.
  -- -> have thereom: ∀ dag: ∃ topo sort
  --
  -- noncomputable def run (n : network) :=
  -- let p := n.prec in
  -- let topo := classical.choice theorem in
  --
  -- still need show that the result of running will still be the same no matter which topo we get.
  -- noncomputable func arent same-in-same-out
  --
  -- the core of the determinism-proof is the fact that run is the same no matter which topo order we get.

  protected theorem topological_sort_correctness (g : dag ι δ ε) :
    g.has_topological_order (topological_sort g) :=
    begin
      unfold has_topological_order,
      intros,
      unfold topological_sort,
      unfold topological_sort',
      simp,
      by_cases h_empty : g.val.ids.nonempty,
        {
          sorry
        },
        {
          sorry
        },
    end

end dag