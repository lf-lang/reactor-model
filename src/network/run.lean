import network.basic
import network.precedence
import graphs.dag

namespace network

  variables {c : ℕ} {n : network c}

  private def run' (topo : list (precedence.graph.reaction_id n)) : (network c) × list (precedence.graph.reaction_id n)
    := sorry
    -- # How do reactor networks run?
    -- # Is it just sequential execution of the reactions that fire?
    -- # Do we need an event queue already for this?

  variable (n)
  def run (h : (precedence.graph.from n).is_acyclic) : network c :=
    let pg := precedence.graph.from n in
    let topo := dag.topological_sort ⟨pg, h⟩ in
    (run' topo).1

  protected theorem determinism (n n' : network c) (h : (precedence.graph.from n).is_acyclic) (h' : (precedence.graph.from n').is_acyclic) :
    n = n' → run n h = run n' h' :=
    begin
      intro hn,
      subst hn,
    end

  -- Execution of the reactor network needs to be the same no matter which concrete topo-list it gets.
  --
  -- noncomputable def run (n : network) :=
  -- let p := n.prec in
  -- let topo := classical.choice theorem in
  --
  -- still need show that the result of running will still be the same no matter which topo we get.
  -- noncomputable func arent same-in-same-out
  --
  -- the core of the determinism-proof is the fact that run is the same no matter which topo order we get.

end network