import inst.exec.propagation.edges
open reactor.ports
open inst.network

variables {υ : Type*} [decidable_eq υ]
















-- For all edges `e` with `e.src = p`, set `e.dst` to `v`.  
private noncomputable def propagate_port (η : graph υ) (p : port.id) : graph υ := 
  propagate_edges η (η.eₒ p).val.to_list 

lemma propagate_port_equiv (η : graph υ) (p : port.id) :
  propagate_port η p ≈ η :=
  begin
    unfold propagate_port,
    induction (η.eₒ p).val.to_list
      ; apply propagate_edges_equiv
  end

lemma propagate_port_out_inv (η : graph υ) {p : port.id}  :
  ∀ o, (propagate_port η p).port role.output o = η.port role.output o :=
  by apply propagate_edges_out_inv

lemma propagate_port_unique_ins_inv (η : graph υ) (p : port.id) (hᵤ : η.has_unique_port_ins) :
  (propagate_port η p).has_unique_port_ins :=
  begin
    have h, from propagate_port_equiv η p,
    exact graph.eq_edges_unique_port_ins (graph.equiv_symm h).left hᵤ
  end

lemma propagate_port_comm (η : graph υ) (p p' : port.id) (hᵤ : η.has_unique_port_ins) : 
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




















-- For all edges `e` with `e.src ∈ p`, set `e.dst` to `rtr.output.nth e.src`.  
noncomputable def propagate_ports (η : graph υ) (p : finset port.id) : graph υ :=
  p.val.to_list.foldl (λ η' p', propagate_edges η' (η'.eₒ p')) η

lemma propagate_ports_out_inv (η : graph υ) {p : finset port.id}  :
  ∀ o, (propagate_ports η p).port role.output o = η.port role.output o :=
  begin
    intro o,
    unfold propagate_ports,
    induction p generalizing η,
      simp,
      rw [list.foldl_cons, p_ih, propagate_port_out_inv]
  end

lemma propagate_ports_comm (η : graph υ) (p p' : finset port.id) (hᵤ : η.has_unique_port_ins) (hₚ : p' ~ p) :
  propagate_ports η p = propagate_ports η p' :=
  begin
    unfold propagate_ports,
    induction hₚ generalizing η,
      case list.perm.nil {
        refl,
      },
      case list.perm.cons : _ _ _ _ hᵢ {
        unfold list.foldl,
        apply hᵢ (propagate_port η hₚ_x), 
        exact propagate_port_unique_ins_inv _ _ hᵤ
      },
      case list.perm.swap {
        unfold list.foldl,
        rw propagate_port_comm η _ _ hᵤ
      },
      case list.perm.trans : l₁ l₂ l₃ p₁ p₂ hᵢ₁ hᵢ₂ {
        exact (hᵢ₂ _ hᵤ).trans (hᵢ₁ _ hᵤ)
      }
  end

lemma propagate_ports_comm' (η : graph υ) (p p' : finset port.id) (hᵤ : η.has_unique_port_ins) :
  propagate_ports (propagate_ports η p) p' = propagate_ports (propagate_ports η p') p :=
  begin
    unfold propagate_ports,
    conv_lhs { rw ←list.foldl_append },
    conv_rhs { rw ←list.foldl_append },
    apply propagate_ports_comm _ _ _ hᵤ list.perm_append_comm
  end 

lemma propagate_ports_equiv (η η' : graph υ) (p : finset port.id) (h : η ≈ η') :
  propagate_ports η p ≈ η' :=
  begin
    induction p with pₕ pₜ hᵢ generalizing η,
      case list.nil {
        unfold propagate_ports,
        exact h
      },
      case list.cons {
        unfold propagate_ports,
        have hₑ, from propagate_port_equiv η pₕ,
        have hₑ', from graph.equiv_trans hₑ h,
        have hᵢ', from hᵢ (propagate_port η pₕ),
        exact hᵢ' hₑ'
      }
  end