import data.rel
import reactor.basic
import split_digraph
open classical

namespace reactor 

  namespace network

    def in_port  {c : ℕ} (ns : vector reactor c) := Σ i : fin c, fin (ns.nth i).nᵢ
    def out_port {c : ℕ} (ns : vector reactor c) := Σ i : fin c, fin (ns.nth i).nₒ

  end network
  open network

  -- By defining the `reactors` as a list instead of a set, we remove the need for identifiers and
  -- use the index into the list as a reactor's identifier.
  structure network (c : ℕ) :=
    (nodes : vector reactor c)
    (graph : split_digraph (out_port nodes) (in_port nodes))
    (unique_ins : graph.is_input_unique)  
    (acylic : graph.is_acyclic) -- to be removed

  namespace network

    -- https://courses.cs.washington.edu/courses/cse326/03wi/lectures/RaoLect20.pdf
    def topo_order {c : ℕ} (n : network c) : list (fin c) := sorry

    private def run' {c : ℕ} (n : network c) (topo : list (fin c)) : (network c) × list (fin c) :=
    begin
      cases topo,
        case nil { exact ⟨n, []⟩ },
        case : h t {
          let hrun := h.run,
          let h' := hrun ⟨h.inputs, h.outputs, h.st⟩,

        }
    end

    def run {c : ℕ} (n : network c) : network c := 
      (run' n (topo_order n)).1

    -- reactor.network.process should use the fixed-point approach from *dataflow with firing*.
    -- reaching a fixed point is equivalent to the global reaction-queue being computed until it is empty
    -- (which would then induce the next time-stamp to be run. without actions a reactor system will only have
    -- one time stamp (because there are no actions to increase them), so the fixed point is a static final state?)

    -- order.basic contains a definition of `monotone`
    -- order.directed contains a definition of `directed`

  end network

end reactor