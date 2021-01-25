import network.graph
import run.propagate_edge

open network

noncomputable def propagate_edges : network.graph → list graph.edge → network.graph :=
  list.foldl propagate_edge

lemma propagate_edges_equiv (η : network.graph) (e : list network.graph.edge) :
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
        exact trans_of (≈) h' h
      } 
  end

lemma propagate_edges_out_inv (η : network.graph) {e : list graph.edge}  :
  ∀ o, (propagate_edges η e).output o = η.output o :=
  begin
    intro o,
    unfold propagate_edges,
    induction e generalizing η,
      simp,
      rw [list.foldl_cons, e_ih, propagate_edge_out_inv]
  end

lemma propagate_edges_unique_ins_inv (η : network.graph) (e : list graph.edge) (hᵤ : η.has_unique_port_ins) :
  (propagate_edges η e).has_unique_port_ins :=
  begin
    have h, from propagate_edges_equiv η e,
    exact network.graph.edges_inv_unique_port_ins_inv (symm h).left hᵤ
  end

lemma propagate_edges_comm (η : network.graph) (hᵤ : η.has_unique_port_ins) (e e' : list graph.edge) (hₘ : ∀ x ∈ e, x ∈ η) (hₚ : e ~ e') :
  propagate_edges η e = propagate_edges η e' :=
  begin
    have hₘ' : ∀ x ∈ e', x ∈ η, {
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
            exact graph.mem_equiv_trans _ _ _ (propagate_edge_equiv _ x) (hₘ_l₁ _ hₓ)
          },
          by { 
            cases list.forall_mem_cons.mp hₘ' with _ hₘ_l₂,
            intros x hₓ, 
            exact graph.mem_equiv_trans _ _ _ (propagate_edge_equiv _ x) (hₘ_l₂ _ hₓ) 
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

lemma propagate_edges_append (η : network.graph) (e e' : list graph.edge) :
  propagate_edges (propagate_edges η e) e' = propagate_edges η (e ++ e') :=
  by simp [propagate_edges, list.foldl_append]
