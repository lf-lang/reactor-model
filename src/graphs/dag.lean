import graphs.digraph

variables (ι δ : Type*) (ε : Π is : finset ι, ({ i // i ∈ is } → δ) → Type*)
variables [∀ i d, digraph.edge (ε i d) ι]

-- A directed acyclic graph, aka DAG. 
def dag := { d : digraph ι δ ε // d.is_acyclic } 

namespace dag 

  variables {ι δ ε} [decidable_eq ι]

  -- The definition of what it means for a given list to be a topological order of a given DAG.
  def topological_order (g : dag ι δ ε) (l : list ι) : Prop :=
    ∀ i i' ∈ l, (i-g.val->i') → (l.index_of i < l.index_of i')

  -- For any DAG there exists a list which is a topological order of the DAG.
  theorem any_dag_has_topo : 
    ∀ g : dag ι δ ε, ∃ l : list ι, topological_order g l :=
    sorry

end dag