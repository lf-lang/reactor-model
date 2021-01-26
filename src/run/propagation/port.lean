import network.graph
import run.propagation.edges

open network

-- For all edges `e` with `e.src = p`, set `e.dst` to `v`.  
noncomputable def propagate_port (η : network.graph) (p : port.id) : network.graph := 
  propagate_edges η (η.edges_out_of p).val.to_list 

lemma propagate_port_equiv (η : network.graph) (p : port.id) :
  propagate_port η p ≈ η :=
  begin
    unfold propagate_port,
    induction (η.edges_out_of p).val.to_list
      ; apply propagate_edges_equiv
  end

lemma propagate_port_out_inv (η : network.graph) {p : port.id}  :
  ∀ o, (propagate_port η p).output o = η.output o :=
  by apply propagate_edges_out_inv

lemma propagate_port_unique_ins_inv (η : network.graph) (p : port.id) (hᵤ : η.has_unique_port_ins) :
  (propagate_port η p).has_unique_port_ins :=
  begin
    have h, from propagate_port_equiv η p,
    exact network.graph.edges_inv_unique_port_ins_inv (symm h).left hᵤ
  end

lemma propagate_port_comm (η : network.graph) (p p' : port.id) (hᵤ : η.has_unique_port_ins) : 
  propagate_port (propagate_port η p) p' = propagate_port (propagate_port η p') p :=
  begin
    unfold propagate_port,
    have h : ∀ x x', (propagate_edges η (η.edges_out_of x).val.to_list).edges_out_of x' = η.edges_out_of x', {
      intros x x',
      unfold graph.edges_out_of,
      rw (propagate_edges_equiv η _).left,
    },
    conv_lhs { rw [h, propagate_edges_append] },
    conv_rhs { rw [h, propagate_edges_append] },
    suffices hₘ_l : ∀ x ∈ ((η.edges_out_of p).val.to_list ++ (η.edges_out_of p').val.to_list), x ∈ η,
    from propagate_edges_comm _ hᵤ _ _ hₘ_l list.perm_append_comm,
    rw list.forall_mem_append,
    split
      ; {
        intro x,
        rw multiset.mem_to_list,
        exact (graph.edges_out_of_mem η _) x,
      }
  end