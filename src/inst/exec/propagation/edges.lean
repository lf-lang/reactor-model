import inst.network.graph
open reactor.ports

-- Cf. inst/primitives.lean
variables {υ : Type*} [decidable_eq υ]

namespace inst
namespace network
namespace graph

  -- Propagates the source value to the desination port for a given edge.
  noncomputable def propagate_edge (η : graph υ) (e : graph.edge) : graph υ := 
    η.update_port role.input e.dst (η.port role.output e.src)

  -- Propagating an edge produces an equivalent network graph.
  lemma propagate_edge_equiv (η : graph υ) (e : graph.edge) : propagate_edge η e ≈ η :=
    by simp [propagate_edge, graph.equiv_symm, graph.update_port_equiv]

  -- Propagating an edge that ends in a port which is independent of a given reaction,
  -- produces a reactor which is equal relative to that reaction.
  lemma propagate_edge_eq_rel_to {η : graph υ} {i : reaction.id} {e : graph.edge} (h : e.dst ∉ η.deps i role.input) :
    (η.propagate_edge e).rtr i.rtr =i.rcn= η.rtr i.rtr :=
    begin
      unfold propagate_edge update_port,
      by_cases hc : i.rtr = e.dst.rtr,
        {
          have hₘ, from (not_iff_not.mpr mem_deps_iff_mem_rcn_deps).mp h,
          have hₘ', from not_and.mp hₘ hc,
          unfold reaction.deps at hₘ',
          simp only [rcn, hc, update_reactor_eq_rtr] at hₘ' ⊢,
          have hₑ, from reactor.eq_rel_to.single (refl ((η.rtr e.dst.rtr).update role.input e.dst.prt (η.port role.output e.src))) hₘ',
          exact reactor.eq_rel_to_symm hₑ
        },
        {
          rw update_reactor_ne_rtr _ _ (ne.symm hc),
          exact reactor.eq_rel_to_refl _ _
        }
    end

  -- Propagates the source values to the desination ports for a given set of edges.
  noncomputable def propagate_edges (η : graph υ) (es : list graph.edge) : graph υ := 
    es.foldl propagate_edge η

  -- Propagating edges produces an equivalent network graph.
  lemma propagate_edges_equiv (η : graph υ) (es : list graph.edge) : propagate_edges η es ≈ η :=
    begin
      unfold propagate_edges,
      induction es generalizing η,
        case list.nil { simp },
        case list.cons : eₕ eₜ hᵢ {
          rw list.foldl_cons,
          transitivity,
            exact hᵢ (propagate_edge η eₕ),
            exact propagate_edge_equiv η eₕ
        } 
    end

  -- Propagating edges that end in ports which are independent of a given reaction,
  -- produces a reactor which is equal relative to that reaction.
  lemma propagate_edges_eq_rel_to {η : graph υ} {i : reaction.id} {es : list graph.edge} (h : ∀ e : graph.edge, e ∈ es → e.dst ∉ η.deps i role.input) :
    (η.propagate_edges es).rtr i.rtr =i.rcn= η.rtr i.rtr :=
    begin
      unfold propagate_edges,
      induction es generalizing η,
        case list.nil { exact reactor.eq_rel_to_refl (η.rtr i.rtr) i.rcn },
        case list.cons {
          rw list.foldl_cons,
          have hᵣ, from propagate_edge_eq_rel_to (h es_hd (list.mem_cons_self _ _)),
          unfold deps rcn at h,
          have hq, from propagate_edge_equiv η es_hd,
          rw ←(hq.right.right i.rtr).right at h,
          have hₘ : ∀ (e : edge), e ∈ es_tl → e.dst ∉ (η.propagate_edge es_hd).deps i role.input, {
            intros e hₑ,
            exact h e (list.mem_cons_of_mem _ hₑ)
          },
          exact reactor.eq_rel_to.multiple (es_ih hₘ) hᵣ
        }
    end

  /-lemma equiv_edges_mem_trans (η η' : graph υ) (e : graph.edge) (h : η ≈ η') :
    e ∈ η.edges → e ∈ η'.edges := 
    begin
      intro hₘ,
      simp [(∈)],
      rw ←h.left,
      exact hₘ
    end

  lemma propagate_edge_comm (η : graph υ) (e e' : graph.edge) (hᵤ : η.has_unique_port_ins) (hₘ : e ∈ η.edges) (hₘ' : e' ∈ η.edges) : 
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

  lemma propagate_edges_comm (η : graph υ) (hᵤ : η.has_unique_port_ins) (e e' : finset graph.edge) (hₘ : ∀ x ∈ e, x ∈ η.edges) (hₚ : e ~ e') :
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

  lemma propagate_edges_append (η : graph υ) (es es' : finset graph.edge) :
    propagate_edges (propagate_edges η e) e' = propagate_edges η (e ++ e') :=
    by simp [propagate_edges, list.foldl_append]-/

end graph
end network
end inst