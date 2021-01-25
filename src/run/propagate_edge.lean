import network.graph

open network

noncomputable def propagate_edge (η : network.graph) (e : graph.edge) : network.graph := 
  η.update_input e.dst (η.output e.src)

lemma propagate_edge_equiv (η : network.graph) (e : graph.edge) :
  propagate_edge η e ≈ η :=
  begin
    unfold propagate_edge,
    apply graph.update_input_equiv
  end

lemma propagate_edge_unique_ins_inv (η : network.graph) (e : graph.edge) (hᵤ : η.has_unique_port_ins) :
  (propagate_edge η e).has_unique_port_ins :=
  begin
    have h, from propagate_edge_equiv η e,
    exact network.graph.edges_inv_unique_port_ins_inv (symm h).left hᵤ
  end

lemma propagate_edge_out_inv (η : network.graph) (e : graph.edge) :
  ∀ o, (propagate_edge η e).output o = η.output o :=
  begin
    intro o,
    unfold propagate_edge,
    apply graph.update_input_out_inv
  end

lemma propagate_edge_comm (η : network.graph) (e e' : graph.edge) (hᵤ : η.has_unique_port_ins) (hₘ : e ∈ η) (hₘ' : e' ∈ η) : 
  propagate_edge (propagate_edge η e) e' = propagate_edge (propagate_edge η e') e :=
  begin
    by_cases h : e = e',
      rw h,
      {
        rw graph.has_unique_port_ins at hᵤ,
        replace h : e ≠ e' := by exact h,
        have h_d : e.dst ≠ e'.dst, from hᵤ _ _ hₘ hₘ' h,
        unfold propagate_edge,
        conv_lhs { rw graph.update_input_out_inv },
        conv_rhs { rw graph.update_input_out_inv },
        rw graph.update_input_comm h_d _ _ η
      }
  end