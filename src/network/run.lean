import digraph
import network.basic
import network.precedence
import network.ids
import network.algorithms

namespace network

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

  private noncomputable def propagate_edges : network.graph → list graph.edge → network.graph :=
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

  -- For all edges `e` with `e.src = p`, set `e.dst` to `v`.  
  private noncomputable def propagate_port (η : network.graph) (p : port.id) : network.graph := 
    propagate_edges η (η.edges_out_of p).val.to_list 

  lemma propagate_port_equiv (η : network.graph) (p : port.id) :
    propagate_port η p ≈ η :=
    begin
      unfold propagate_port,
      induction (η.edges_out_of p).val.to_list
        ; apply propagate_edges_equiv
    end

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

  -- For all edges `e` with `e.src ∈ p`, set `e.dst` to `rtr.output.nth e.src`.  
  private noncomputable def propagate_ports : network.graph → list port.id → network.graph :=
    list.foldl propagate_port

  lemma propagate_ports_comm (η : network.graph) (p p' : list port.id) (hᵤ : η.has_unique_port_ins) (hₚ : p' ~ p) :
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

  lemma propagate_ports_comm' (η : network.graph) (p p' : list port.id) (hᵤ : η.has_unique_port_ins) :
    propagate_ports (propagate_ports η p) p' = propagate_ports (propagate_ports η p') p :=
    begin
      unfold propagate_ports,
      conv_lhs { rw ←list.foldl_append },
      conv_rhs { rw ←list.foldl_append },
      apply propagate_ports_comm _ _ _ hᵤ list.perm_append_comm
    end 

  lemma propagate_ports_equiv (η η' : network.graph) (p : list port.id) (h : η ≈ η') :
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
          have hₑ', from trans_of (≈) hₑ h,
          have hᵢ', from hᵢ (propagate_port η pₕ),
          exact hᵢ' hₑ'
        }
    end

  private noncomputable def propagate_output (η : network.graph) (i : reactor.id) (p : list ℕ) : network.graph :=
    propagate_ports η (p.map (λ x, {rtr := i, prt := x}))
    
  lemma propagate_output_equiv (η η' : network.graph) (i : reactor.id) (p : list ℕ) (h : η ≈ η') :
    propagate_output η i p ≈ η' :=
    begin
      unfold propagate_output,
      induction (p.map (λ x, {port.id . rtr := i, prt := x}))
        ; apply propagate_ports_equiv
        ; exact h
    end

  lemma propagate_output_comm (η : network.graph) (i i' : reactor.id) (p p' : list ℕ) (hᵤ : η.has_unique_port_ins) :
    propagate_output (propagate_output η i p) i' p' = propagate_output (propagate_output η i' p') i p :=
    propagate_ports_comm' _ _ _ hᵤ

  private noncomputable def run_reaction (η : network.graph) (i : reaction.id) : network.graph :=
    propagate_output 
      (η.update_reactor i.rtr ((η.rtr i.rtr).run i.rcn) (reactor.run_equiv _ _))
      i.rtr
      ((η.rtr i.rtr).ports_affected_by i.rcn)
      
  lemma run_reaction_equiv (η : network.graph) (i : reaction.id) :
    run_reaction η i ≈ η :=
    begin
      unfold run_reaction,
      apply propagate_output_equiv,
      apply graph.update_reactor_equiv
    end

  -- If there is no path between two reactions in a precedence graph, then they are independent,
  -- i.e. their order of execution doesn't matter.
  lemma run_reaction_comm (η : network.graph) (hᵤ : η.has_unique_port_ins) (ρ : precedence.graph) (h_wf : ρ.is_well_formed_over η) (i i' : reaction.id) :
    ¬(i~ρ~>i') → ¬(i'~ρ~>i) → run_reaction (run_reaction η i) i' = run_reaction (run_reaction η i') i :=
    begin 
      intros hₚ hₚ',
      unfold run_reaction,
      
      -- for the results of run_reaction to be different, 
      -- either (A) the commutativity of propagate_output would need to break
      -- or (B) the intermediate (run) reactors would have to be different, which is only possible if their state or input differs
      --
      -- for (A) to break, the destinations of two reactions would have to be equal, which ...
      
    end

  private noncomputable def run_topo : network.graph → list reaction.id → network.graph :=
    list.foldl run_reaction

  lemma run_topo_equiv (η : network.graph) (t : list reaction.id) :
    run_topo η t ≈ η :=
    begin
      induction t with tₕ tₜ hᵢ generalizing η,
        case list.nil {
          unfold run_topo,
          exact refl_of (≈) η
        },
        case list.cons {
          unfold run_topo,
          have hₑ, from run_reaction_equiv η tₕ,
          have hᵢ', from hᵢ (run_reaction η tₕ),
          exact trans_of (≈) hᵢ' hₑ
        }
    end

  lemma run_topo_unique_ports_inv (n : network) (topo : list reaction.id) : 
    (run_topo n.η topo).has_unique_port_ins :=
    begin
      have h, from run_topo_equiv n.η topo,
      exact network.graph.edges_inv_unique_port_ins_inv (symm h).left n.unique_ins
    end 
    
  lemma run_topo_prec_acyc_inv (n : network) (topo : list reaction.id) : 
    (run_topo n.η topo).is_prec_acyclic :=
    begin
      have h, from run_topo_equiv n.η topo,
      exact network.graph.equiv_prec_acyc_inv (symm h) n.prec_acyclic
    end 

  theorem run_topo_comm (η : network.graph) (ρ : precedence.graph) (h_a : ρ.is_acyclic) (h_w : ρ.is_well_formed_over η) :
    ∀ (t t') (h_t : ρ.topological_order h_a t) (h_t' : ρ.topological_order h_a t'), run_topo η t = run_topo η t' :=
    begin
      intros t t' h_t h_t',
      induction t generalizing η,
        -- run_topo := foldl run_reaction
        -- if we 
    end

  private noncomputable def run_aux (n : network) (t : list reaction.id) : network :=
    {η := run_topo n.η t, unique_ins := run_topo_unique_ports_inv n t, prec_acyclic := run_topo_prec_acyc_inv n t}

  noncomputable def run (n : network) (fₚ : prec_func) (fₜ : topo_func) : network :=
    run_aux n (fₜ (fₚ n))

  theorem run_equiv (n : network) (fₚ : prec_func) (fₜ : topo_func) :
    (n.run fₚ fₜ).η ≈ n.η :=
    begin
      unfold run run_aux,
      simp,
      apply run_topo_equiv
    end

  theorem determinism (n : network) (p p' : prec_func) (t t' : topo_func) :
    n.run p t = n.run p' t' := 
    begin
      rw all_prec_funcs_are_eq p p',
      unfold run run_aux,
      suffices h : run_topo n.η (t (p' n)) = run_topo n.η (t' (p' n)), {
        ext1,
        simp,
        exact h
      },
      have h_pnw : (p' n).is_well_formed_over n.η, from p'.well_formed n,
      have h_pna : (p' n).is_acyclic, from n.prec_acyclic (p' n) h_pnw,
      have h_t   : (p' n).topological_order h_pna (t (p' n)), from t.is_topo _ _ h_pnw,
      have h_t'  : (p' n).topological_order h_pna (t' (p' n)), from t'.is_topo _ _ h_pnw,
      exact run_topo_comm n.η _ h_pna h_pnw _ _ h_t h_t'
    end

end network