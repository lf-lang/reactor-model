import reactor.network.basic
import reactor.network.precedence
import graphs.dag

namespace reactor
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

end network
end reactor