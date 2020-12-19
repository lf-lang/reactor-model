import data.rel
import reactor.basic

namespace reactor 

  namespace network

    class node :=
      (nᵢ nₒ nₛ : ℕ)
      (inputs : ports nᵢ)
      (outputs : ports nₒ)
      (st : state nₛ)
      (run : (ports nᵢ) × (ports nₒ) × (state nₛ) → (ports nᵢ) × (ports nₒ) × (state nₛ)) -- workaround for `node → node`

    private def node_func {nᵢ nₒ nₛ : ℕ} (r : reactor nᵢ nₒ nₛ) : (ports nᵢ) × (ports nₒ) × (state nₛ) → (ports nᵢ) × (ports nₒ) × (state nₛ) :=
      λ input, 
        let rᵢ : reactor nᵢ nₒ nₛ := ⟨input.1, input.2.1, input.2.2, r.rs⟩ in
        let rₒ := run rᵢ in
        ⟨rₒ.inputs, rₒ.outputs, rₒ.st⟩ 

    -- Reactors are nodes.
    instance {nᵢ nₒ nₛ : ℕ} {r : reactor nᵢ nₒ nₛ} : node := 
      ⟨nᵢ, nₒ, nₛ, r.inputs, r.outputs, r.st, node_func r⟩

    def in_port  {c : ℕ} (ns : vector node c) := Σ i : fin c, fin (ns.nth i).nᵢ
    def out_port {c : ℕ} (ns : vector node c) := Σ i : fin c, fin (ns.nth i).nₒ

  end network
  open network

  /--
  inductive path {α β₁ β₂ : Type*} {r : rel (α × β₁) (α × β₂)} : 
    | single (src : α × β₁) (dst : α × β₂) (edge : r src dst) : path
    | step (src : α × β₁) (path ) : path
  -/



  -- By defining the `reactors` as a list instead of a set, we remove the need for identifiers and
  -- use the index into the list as a reactor's identifier.
  structure network (c : ℕ) :=
    (nodes : vector node c)
    (edges : rel (out_port nodes) (in_port nodes))
    -- (acylic : ∀ (o : out_port nodes) (i : in_port nodes), edges o i → o.1 ≠ i.1)
    (unique_ins : ∀ (o₁ o₂ : out_port nodes) (i : in_port nodes), (edges o₁ i) ∧ (edges o₂ i) → o₁ = o₂)  

  namespace network

    def topo_order {c: ℕ} (n : network c) : list (fin c) := sorry -- topo sort

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

asd