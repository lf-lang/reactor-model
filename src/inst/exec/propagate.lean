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

  -- Propagating an edge that ends in a port, which is independent of a given reaction,
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

  lemma propagate_edge_run_local_comm {η : graph υ} {e : graph.edge} {i : reaction.id} 
    (hᵢ : e.dst ∉ η.deps i role.input) (hₒ : e.src ∉ η.deps i role.output) :
    (η.propagate_edge e).run_local i = (η.run_local i).propagate_edge e :=
    sorry

  -- Under the right conditions, the order in which edges are propagated can be swapped.
  lemma propagate_edge_comm {η : network.graph υ} {e e' : graph.edge} (hᵤ : η.has_unique_port_ins) (hₘ : e ∈ η.edges) (hₘ' : e' ∈ η.edges) : 
    propagate_edge (propagate_edge η e) e' = propagate_edge (propagate_edge η e') e :=
    begin
      by_cases h : e = e',
        rw h,
        {
          unfold propagate_edge,
          repeat { rw update_port_opposite_eq },
          rw update_port_comm,
          rw graph.has_unique_port_ins at hᵤ,
          exact (hᵤ _ _ hₘ hₘ' h)
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

  -- Propagating edges that end in ports, which are independent of a given reaction,
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
          suffices hₘ : ∀ (e : edge), e ∈ es_tl → e.dst ∉ (η.propagate_edge es_hd).deps i role.input, 
          from reactor.eq_rel_to.multiple (es_ih hₘ) hᵣ,
          intros e hₑ,
          have hq, from propagate_edge_equiv η es_hd,
          rw [deps, rcn, ←(hq.right.right i.rtr).right] at h,
          exact h e (list.mem_cons_of_mem _ hₑ)
        }
    end

  -- Under the right conditions, running a reactor and propagating edges can be swapped in their order.
  lemma propagate_edges_run_local_comm {η : graph υ} {es : list graph.edge} {i : reaction.id} 
    (h : ∀ e : edge, e ∈ es → (e.dst ∉ η.deps i role.input) ∧ (e.src ∉ η.deps i role.output)) :
    (η.propagate_edges es).run_local i = (η.run_local i).propagate_edges es :=
    begin
      induction es generalizing η,
        case list.nil { simp [propagate_edges] },
        case list.cons {
          simp only [propagate_edges, list.foldl_cons] at es_ih ⊢,
          have h', from h es_hd (list.mem_cons_self _ _),
          rw ←(propagate_edge_run_local_comm h'.left h'.right),
          suffices hg : ∀ (e : edge), e ∈ es_tl → e.dst ∉ (η.propagate_edge es_hd).deps i role.input ∧ e.src ∉ (η.propagate_edge es_hd).deps i role.output, 
          from es_ih hg,
          intros e hₑ, 
          replace h := h e (list.mem_cons_of_mem _ hₑ),
          unfold deps rcn at h,
          have hq, from propagate_edge_equiv η es_hd,
          rw ←(hq.right.right i.rtr).right at h,
          exact h
        }
    end

  -- Under the right conditions, the order in which edges are propagated can be swapped.
  lemma propagate_edges_comm' {η : graph υ} {es : list graph.edge} {e : graph.edge} (hᵤ : η.has_unique_port_ins) (hₘ : e ∈ η.edges) (hₘ' : ∀ e' ∈ es, e' ∈ η.edges) : 
    (η.propagate_edges es).propagate_edge e = (η.propagate_edge e).propagate_edges es :=
    begin
      induction es generalizing η,
        case list.nil { simp [propagate_edges] },
        case list.cons {
          simp only [propagate_edges, list.foldl_cons] at es_ih ⊢,
          have h', from hₘ' es_hd (list.mem_cons_self _ _),
          rw propagate_edge_comm hᵤ hₘ h',
          have hᵤ' : (η.propagate_edge es_hd).has_unique_port_ins, 
          from eq_edges_unique_port_ins (propagate_edge_equiv η es_hd).left hᵤ,
          suffices hg : ∀ (e' : edge), e' ∈ es_tl → e' ∈ η.edges, 
          from es_ih hᵤ' hₘ hg,
          intros e' hₑ,
          exact hₘ' e' (list.mem_cons_of_mem _ hₑ)
        }
    end

  -- Under the right conditions, the order in which edges are propagated can be swapped.
  lemma propagate_edges_comm {η : graph υ} {es es' : list graph.edge} (hᵤ : η.has_unique_port_ins) (hₘ : ∀ e ∈ es, e ∈ η.edges) (hₘ' : ∀ e' ∈ es', e' ∈ η.edges) :
    (η.propagate_edges es).propagate_edges es' = (η.propagate_edges es').propagate_edges es :=
    begin
      induction es generalizing η,
        case list.nil { simp [propagate_edges] },
        case list.cons {
          simp only [propagate_edges, list.foldl_cons] at es_ih ⊢,
          have hc, from propagate_edges_comm' hᵤ (hₘ es_hd (list.mem_cons_self _ _)) hₘ',
          rw propagate_edges at hc,
          simp only [hc, propagate_edges],
          have hᵤ' : (η.propagate_edge es_hd).has_unique_port_ins, 
          from eq_edges_unique_port_ins (propagate_edge_equiv η es_hd).left hᵤ,
          suffices hg : ∀ (e : edge), e ∈ es_tl → e ∈ η.edges, 
          from es_ih hᵤ' hg hₘ',
          intros e hₑ,
          exact hₘ e (list.mem_cons_of_mem _ hₑ)
        }
    end

  -- For all edges `e` with `e.src = p`, set `e.dst` to `v`.  
  noncomputable def propagate_port (η : graph υ) (p : port.id) : graph υ := 
    η.propagate_edges (η.eₒ p).val.to_list 

  -- Propagating a port produces an equivalent network graph.
  lemma propagate_port_equiv (η : graph υ) (p : port.id) : propagate_port η p ≈ η :=
    begin
      unfold propagate_port,
      induction (η.eₒ p).val.to_list
        ; apply propagate_edges_equiv
    end

  -- Propagating a port that connects only to ports, which are independent of a given reaction,
  -- produces a reactor which is equal relative to that reaction.
  lemma propagate_port_eq_rel_to {η : graph υ} {i : reaction.id} {p : port.id} (h : ∀ e : edge, e ∈ η.eₒ p → e.dst ∉ η.deps i role.input) :
    (η.propagate_port p).rtr i.rtr =i.rcn= η.rtr i.rtr :=
    begin
      unfold propagate_port,
      suffices h' : ∀ (e : edge), e ∈ (η.eₒ p).val.to_list → e.dst ∉ η.deps i role.input, 
      from propagate_edges_eq_rel_to h',
      intros e hₑ,
      rw multiset.mem_to_list at hₑ,
      exact h e hₑ
    end

  -- Under the right conditions, running a reactor and propagating a port can be swapped in their order.
  lemma propagate_port_run_local_comm {η : graph υ} {p : port.id} {i : reaction.id} 
    (h : ∀ e : edge, (e ∈ η.eₒ p) → (e.dst ∉ η.deps i role.input) ∧ (e.src ∉ η.deps i role.output)) :
    (η.propagate_port p).run_local i = (η.run_local i).propagate_port p :=
    begin
      unfold propagate_port,
      suffices hg : ∀ (e : edge), e ∈ (η.eₒ p).val.to_list → e.dst ∉ η.deps i role.input ∧ e.src ∉ η.deps i role.output, 
      from propagate_edges_run_local_comm hg,
      intros e hₑ,
      rw multiset.mem_to_list at hₑ, 
      exact h e hₑ
    end

  -- Under the right conditions, the order in which ports are propagated can be swapped.
  lemma propagate_port_comm {η : graph υ} (p p' : port.id) (hᵤ : η.has_unique_port_ins) : 
    propagate_port (propagate_port η p) p' = propagate_port (propagate_port η p') p :=
    begin
      unfold propagate_port,
      have h : ∀ x x', (propagate_edges η (η.eₒ x).val.to_list).eₒ x' = η.eₒ x', {
        intros x x',
        unfold graph.eₒ,
        rw (propagate_edges_equiv η _).left
      },
      repeat { rw h },
      have h' : ∀ x e, e ∈ (η.eₒ x).val.to_list → e ∈ η.edges, {
        intros x e hₑ,
        rw multiset.mem_to_list at hₑ,
        unfold eₒ at hₑ,
        exact (finset.mem_filter.mp hₑ).left
      },
      exact propagate_edges_comm hᵤ (h' p) (h' p')
    end

  -- For all edges `e` with `e.src ∈ ps`, set `e.dst` to `rtr.output.nth e.src`.  
  noncomputable def propagate_ports (η : graph υ) (ps : list port.id) : graph υ :=
    ps.foldl propagate_port η

  -- Propagating ports produces an equivalent network graph.
  lemma propagate_ports_equiv (η : graph υ) (ps : list port.id) : propagate_ports η ps ≈ η :=
    begin
      induction ps with pₕ pₜ hᵢ generalizing η,
        case list.nil { simp [propagate_ports] },
        case list.cons {
          simp only [propagate_ports, list.foldl_cons],
          transitivity,
            exact hᵢ (propagate_port η pₕ),
            exact propagate_port_equiv η pₕ
        }
    end

  -- Propagating ports that connect only to ports, which are independent of a given reaction,
  -- produces a reactor which is equal relative to that reaction.
  lemma propagate_ports_eq_rel_to {η : graph υ} {i : reaction.id} {ps : list port.id} (h : ∀ p ∈ ps, ∀ e : edge, e ∈ η.eₒ p → e.dst ∉ η.deps i role.input) :
    (η.propagate_ports ps).rtr i.rtr =i.rcn= η.rtr i.rtr :=
    begin
      induction ps generalizing η,
        case list.nil {
          unfold propagate_ports,
          exact reactor.eq_rel_to_refl _ _,
        },
        case list.cons {
          simp only [propagate_ports, list.foldl_cons] at ps_ih ⊢,
          have hᵣ, from propagate_port_eq_rel_to (h ps_hd (list.mem_cons_self _ _)),
          simp at hᵣ,
          suffices hₘ : (∀ (p : port.id), p ∈ ps_tl → ∀ (e : edge), e ∈ (η.propagate_port ps_hd).eₒ p → e.dst ∉ (η.propagate_port ps_hd).deps i role.input), 
          from reactor.eq_rel_to.multiple (ps_ih hₘ) hᵣ,
          intros x hₓ e hₑ,
          have hq, from propagate_port_equiv η ps_hd,
          rw [deps, rcn, ←(hq.right.right i.rtr).right] at h,
          rw [eₒ, hq.left] at hₑ,
          exact (h x (list.mem_cons_of_mem _ hₓ) e) hₑ
        }
    end

  -- Under the right conditions, running a reactor and propagating ports can be swapped in their order.
  lemma propagate_ports_run_local_comm {η : graph υ} {ps : list port.id} {i : reaction.id} 
    (h : ∀ (p ∈ ps) (e : edge), (e ∈ η.eₒ p) → e.dst ∉ (η.deps i role.input) ∧ (e.src ∉ η.deps i role.output)) :
    (η.propagate_ports ps).run_local i = (η.run_local i).propagate_ports ps :=
    begin
      induction ps generalizing η,
        case list.nil { simp [propagate_ports] },
        case list.cons {
          simp only [propagate_ports, list.foldl_cons] at ps_ih ⊢,
          have h', from h ps_hd (list.mem_cons_self _ _),
          rw ←(propagate_port_run_local_comm h'),
          suffices hg : ∀ (p : port.id), p ∈ ps_tl → ∀ (e : edge), e ∈ (η.propagate_port ps_hd).eₒ p → e.dst ∉ (η.propagate_port ps_hd).deps i role.input ∧ e.src ∉ (η.propagate_port ps_hd).deps i role.output,
          from ps_ih hg,
          intros p hₚ e hₑ, 
          replace h := h p (list.mem_cons_of_mem _ hₚ) e,
          unfold eₒ at hₑ,
          have hq, from propagate_port_equiv η ps_hd,
          rw hq.left at hₑ,
          replace h := h hₑ,
          unfold deps rcn at h,
          rw ←(hq.right.right i.rtr).right at h,
          exact h
        }
    end

  -- Under the right conditions, the order in which ports are propagated can be swapped.
  lemma propagate_ports_comm' {η : graph υ} (p : port.id) (ps : list port.id) (hᵤ : η.has_unique_port_ins) : 
    (η.propagate_ports ps).propagate_port p = (η.propagate_port p).propagate_ports ps :=
    begin
      induction ps generalizing η,
        case list.nil { simp [propagate_ports] },
        case list.cons {
          simp only [propagate_ports, list.foldl_cons] at ps_ih ⊢,
          rw propagate_port_comm _ _ hᵤ,
          exact ps_ih (eq_edges_unique_port_ins (symm (propagate_port_equiv η ps_hd).left) hᵤ)
        }
    end

  -- Under the right conditions, the order in which ports are propagated can be swapped.
  lemma propagate_ports_comm {η : graph υ} (ps ps' : list port.id) (hᵤ : η.has_unique_port_ins) : 
    (η.propagate_ports ps).propagate_ports ps' = (η.propagate_ports ps').propagate_ports ps :=
    begin
      induction ps generalizing η,
        case list.nil { simp [propagate_ports] },
        case list.cons {
          simp only [propagate_ports, list.foldl_cons] at ps_ih ⊢,
          have hc, from propagate_ports_comm' ps_hd ps' hᵤ,
          rw propagate_ports at hc,
          simp only [hc, propagate_ports],
          from ps_ih (eq_edges_unique_port_ins (symm (propagate_port_equiv η ps_hd).left) hᵤ)
        }
    end

end graph
end network
end inst