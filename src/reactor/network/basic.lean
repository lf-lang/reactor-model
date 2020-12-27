import data.rel
import reactor.basic
import reactor.network.graph

open classical

namespace reactor 

  namespace network

    def in_port  {c : ℕ} (ns : vector reactor c) := Σ i : fin c, fin (ns.nth i).nᵢ
    def out_port {c : ℕ} (ns : vector reactor c) := Σ i : fin c, fin (ns.nth i).nₒ

  end network
  
  --! The `nodes` should really be part of `φ`. 
  --! This is currently not possible, because the network.graph needs to
  --! know the type of it's nodes in order to know the type of its edges.
  --! -> digraph needs to be adjusted to solve this
  structure network (c : ℕ) :=
    (φ : network.graph c)
    (acyclic : φ.is_acyclic)
    (unique : φ.is_input_unique)

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