import inst.network.graph
import inst.exec.propagation.edges

open reactor.ports
open network

variables {υ : Type*} [decidable_eq υ]

-- For all edges `e` with `e.src = p`, set `e.dst` to `v`.  
noncomputable def propagate_port (η : network.graph υ) (p : port.id) : network.graph υ := 
  propagate_edges η (η.eₒ p).val.to_list 

lemma propagate_port_equiv (η : network.graph υ) (p : port.id) :
  propagate_port η p ≈ η :=
  begin
    unfold propagate_port,
    induction (η.eₒ p).val.to_list
      ; apply propagate_edges_equiv
  end

lemma propagate_port_out_inv (η : network.graph υ) {p : port.id}  :
  ∀ o, (propagate_port η p).port role.output o = η.port role.output o :=
  by apply propagate_edges_out_inv

lemma propagate_port_unique_ins_inv (η : network.graph υ) (p : port.id) (hᵤ : η.has_unique_port_ins) :
  (propagate_port η p).has_unique_port_ins :=
  begin
    have h, from propagate_port_equiv η p,
    exact network.graph.eq_edges_unique_port_ins (graph.equiv_symm h).left hᵤ
  end

lemma propagate_port_comm (η : network.graph υ) (p p' : port.id) (hᵤ : η.has_unique_port_ins) : 
  propagate_port (propagate_port η p) p' = propagate_port (propagate_port η p') p :=
  begin
    unfold propagate_port,
    have h : ∀ x x', (propagate_edges η (η.eₒ x).val.to_list).eₒ x' = η.eₒ x', {
      intros x x',
      unfold graph.eₒ,
      rw (propagate_edges_equiv η _).left,
    },
    conv_lhs { rw [h, propagate_edges_append] },
    conv_rhs { rw [h, propagate_edges_append] },
    suffices hₘ_l : ∀ x ∈ ((η.eₒ p).val.to_list ++ (η.eₒ p').val.to_list), x ∈ η.edges,
    from propagate_edges_comm _ hᵤ _ _ hₘ_l list.perm_append_comm,
    rw list.forall_mem_append,
    split
      ; {
        intros x hₓ,
        rw [multiset.mem_to_list, graph.eₒ] at hₓ,
        exact (finset.mem_filter.mp hₓ).left
      }
  end