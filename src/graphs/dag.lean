import nondet
import graphs.digraph

variables (ι δ : Type*) (ε : (ι → δ) → Type*)
variables [decidable_eq δ] [∀ d, digraph.edge (ε d) ι]

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

  theorem exis_ndet_topo_func :
    ∃ f : (dag ι δ ε) ~?> (list ι), ∀ g t, t ∈ (f g) → topological_order g t :=
    sorry

end dag