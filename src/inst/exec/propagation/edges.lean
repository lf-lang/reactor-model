import inst.network.graph
import inst.exec.propagation.edge

open reactor.ports
open network

variables {υ : Type*} [decidable_eq υ]

noncomputable def propagate_edges : network.graph υ → list graph.edge → network.graph υ :=
  list.foldl propagate_edge

lemma propagate_edges_equiv (η : network.graph υ) (e : list network.graph.edge) :
  propagate_edges η e ≈ η :=
  begin
    induction e generalizing η,
      case list.nil {
        simp only [(≈)],
        finish 
      },
      case list.cons : eₕ eₜ hᵢ {
        unfold propagate_edges,
        have h, from propagate_edge_equiv η eₕ,
        have h', from hᵢ (propagate_edge η eₕ),
        exact graph.equiv_trans h' h
      } 
  end

lemma propagate_edges_out_inv (η : network.graph υ) {e : list graph.edge}  :
  ∀ o, (propagate_edges η e).port role.output o = η.port role.output o :=
  begin
    intro o,
    unfold propagate_edges,
    induction e generalizing η,
      simp,
      rw [list.foldl_cons, e_ih, propagate_edge_out_inv]
  end

lemma propagate_edges_unique_ins_inv (η : network.graph υ) (e : list graph.edge) (hᵤ : η.has_unique_port_ins) :
  (propagate_edges η e).has_unique_port_ins :=
  begin
    have h, from propagate_edges_equiv η e,
    exact network.graph.eq_edges_unique_port_ins (graph.equiv_symm h).left hᵤ
  end

lemma equiv_edges_mem_trans (η η' : graph υ) (e : graph.edge) (h : η ≈ η') :
  e ∈ η.edges → e ∈ η'.edges := 
  begin
    intro hₘ,
    simp [(∈)],
    rw ←h.left,
    exact hₘ
  end

lemma propagate_edges_comm (η : network.graph υ) (hᵤ : η.has_unique_port_ins) (e e' : list graph.edge) (hₘ : ∀ x ∈ e, x ∈ η.edges) (hₚ : e ~ e') :
  propagate_edges η e = propagate_edges η e' :=
  begin
    have hₘ' : ∀ x ∈ e', x ∈ η.edges, {
      intros x h,
      exact hₘ _ ((list.perm.mem_iff hₚ).mpr h),
    },
    unfold propagate_edges,
    induction hₚ generalizing η,
      case list.perm.nil {
        refl,
      },
      case list.perm.cons : _ _ _ _ hᵢ {
        unfold list.foldl,
        apply hᵢ (propagate_edge η hₚ_x), 
          exact (propagate_edge_unique_ins_inv _ _ hᵤ),
          by { 
            cases list.forall_mem_cons.mp hₘ with _ hₘ_l₁,
            intros x hₓ, 
            exact equiv_edges_mem_trans _ _ _ (propagate_edge_equiv _ x) (hₘ_l₁ _ hₓ)
          },
          by { 
            cases list.forall_mem_cons.mp hₘ' with _ hₘ_l₂,
            intros x hₓ, 
            exact equiv_edges_mem_trans _ _ _ (propagate_edge_equiv _ x) (hₘ_l₂ _ hₓ) 
          },
      },
      case list.perm.swap {
        unfold list.foldl,
        rw [list.forall_mem_cons, list.forall_mem_cons] at hₘ,
        rcases hₘ with ⟨h1, h2, _⟩,
        rw propagate_edge_comm η _ _ hᵤ h1 h2
      },
      case list.perm.trans : l₁ l₂ l₃ p₁ p₂ hᵢ₁ hᵢ₂ {
        have m := λ x h, hₘ x (p₁.mem_iff.mpr h),
        have m' := λ x h, hₘ' x (p₂.mem_iff.mp h),
        exact (hᵢ₁ _ hᵤ hₘ m).trans (hᵢ₂ _ hᵤ m' hₘ')
      }
  end

lemma propagate_edges_append (η : network.graph υ) (e e' : list graph.edge) :
  propagate_edges (propagate_edges η e) e' = propagate_edges η (e ++ e') :=
  by simp [propagate_edges, list.foldl_append]

lemma propagate_edges_eq_rel (η : network.graph υ) (l : list graph.edge) (i : reaction.id) :
  (∀ e : graph.edge, e ∈ l → ¬(η.rcn_dep_on_prt i e.dst)) → (η.rtr i.rtr).eq_rel_to ((propagate_edges η l).rtr i.rtr) i.rcn :=
  begin
    intro h,
    induction l,
      case list.nil {
        unfold propagate_edges,
        apply reactor.eq_rel_to_refl,
      },
      case list.cons {
        unfold propagate_edges,
        rw list.foldl_cons,
        -- HERE, generalize η?
        have hₑ : (η.rtr i.rtr).eq_rel_to ((propagate_edge η l_hd).rtr i.rtr) i.rcn,
        from propagate_edge_eq_rel _ _ _ (h l_hd (list.mem_cons_self _ _)),
        -- have H, from l_ih (propagate_edge η l_hd)
        have hₘ : ∀ (e : graph.edge), e ∈ l_tl → ¬(propagate_edge η l_hd).rcn_dep_on_prt i e.dst, from sorry,
        exact l_ih (propagate_edge η l_hd) hₘ,
      }
  end