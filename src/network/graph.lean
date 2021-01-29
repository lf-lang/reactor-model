import digraph
import reactor
import network.ids

open reactor

namespace network

  namespace graph
    
    structure edge :=
      (src : port.id)
      (dst : port.id)

    instance digraph_edge : digraph.edge graph.edge reactor.id := 
      { src := (λ e, e.src.rtr), dst := (λ e, e.dst.rtr) }

  end graph

  def graph (υ : Type*) [decidable_eq υ] : Type* := 
    digraph reactor.id (reactor υ) graph.edge

  variables {υ : Type*} [decidable_eq υ]

  namespace graph

    noncomputable instance dec_eq : decidable_eq graph.edge := classical.dec_eq _

    @[reducible]
    instance rtr_mem : has_mem (reactor υ) (graph υ) := {mem := λ d g, ∃ i, g.data i = d}

    @[reducible]
    instance edge_mem : has_mem edge (graph υ) := {mem := λ e η, e ∈ η.edges}

    -- The reactor contained in a network graph, that is associated with a given reaction ID.
    noncomputable def rtr (η : network.graph υ) (i : reactor.id) : reactor υ :=
      η.data i

    instance equiv : has_equiv (graph υ) := ⟨λ η η', η.edges = η'.edges ∧ η.ids = η'.ids ∧ ∀ i, (η.rtr i) ≈ (η'.rtr i)⟩

    instance : is_equiv (graph υ) (≈) := 
      {
        symm := begin simp [(≈)], finish end,
        trans := begin simp [(≈)], finish end,
        refl := by simp [(≈)]
      }

    lemma mem_equiv_trans (η η' : graph υ) (e : edge) (h : η ≈ η') :
      e ∈ η → e ∈ η' := 
      begin
        intro hₘ,
        simp [(∈)],
        rw ←h.left,
        exact hₘ
      end

    -- The reaction contained in a network graph, that is associated with a given reaction ID.
    noncomputable def rcn (η : graph υ) (i : reaction.id) : reaction υ :=
      (η.data i.rtr).reactions i.rcn

    -- The input port in a network graph, that is associated with a given port ID.
    noncomputable def input (η : graph υ) (p : port.id) : option υ :=
      option.join ((η.data p.rtr).input.nth p.prt)

    -- The output port in a network graph, that is associated with a given port ID.
    noncomputable def output (η : graph υ) (p : port.id) : option υ :=
      option.join ((η.data p.rtr).output.nth p.prt)

    noncomputable def dₒ (η : graph υ) (i : reaction.id) : finset port.id :=
      (η.rcn i).dₒ.image (λ p, {port.id . rtr := i.rtr, prt := p})

    noncomputable def edges_out_of (η : graph υ) (p : port.id) : finset graph.edge :=
      η.edges.filter (λ e, (e : graph.edge).src = p)

    noncomputable def update_reactor (η : graph υ) (i : reactor.id) (r : reactor υ) : graph υ :=
      η.update_data i r
      /-
        unique_ins := graph.edges_inv_unique_port_ins_inv (refl _) n.unique_ins,
        prec_acyclic := graph.equiv_prec_acyc_inv (graph.update_with_equiv_rtr_is_equiv _ _ _ h) n.prec_acyclic
      -/

    noncomputable def update_input (η : graph υ) (p : port.id) (v : option υ) : graph υ :=
      update_reactor η p.rtr ((η.data p.rtr).update_input p.prt v)

    noncomputable def update_output (η : graph υ) (p : port.id) (v : option υ) : graph υ :=
      update_reactor η p.rtr ((η.data p.rtr).update_output p.prt v)

    noncomputable def clear_reactor_excluding (η : graph υ) (r : reactor.id) (i : finset port.id) (o : finset port.id) : graph υ :=
      η.update_reactor r ((η.rtr r).clear_ports_excluding (i.image (λ x, x.prt)) (o.image (λ x, x.prt)))

    noncomputable def clear_ports_excluding (η : graph υ) (i : finset port.id) (o : finset port.id) : graph υ :=
      η.ids.val.to_list.foldl (λ η' r, η'.clear_reactor_excluding r (i.filter (λ x, x.rtr = r)) (o.filter (λ x, x.rtr = r))) η

    lemma edges_out_of_mem (η : graph υ) (p : port.id) :
      ∀ e ∈ η.edges_out_of p, e ∈ η :=
      begin
        intros e h,
        simp [edges_out_of, finset.mem_filter] at h,
        exact h.left,
      end

    -- Updating a network graph with an equivalent reactor keeps their `data` equivalent.
    lemma update_with_equiv_rtr_all_data_equiv {η : graph υ} (i : reactor.id) (rtr : reactor υ) :
      η.data i ≈ rtr → ∀ r, η.data r ≈ (η.update_data i rtr).data r :=
      begin
        intros hₑ r,
        simp only [(≈)] at hₑ ⊢,
        unfold digraph.update_data,
        by_cases (r = i)
          ; finish
      end

    -- Updating a network graph with an equivalent reactor produces an equivalent network graph.
    theorem update_with_equiv_rtr_is_equiv (η : graph υ) (i : reactor.id) (rtr : reactor υ) :
      η.data i ≈ rtr → η ≈ η.update_data i rtr :=
      begin
        intro hₑ,
        simp [(≈)] at hₑ ⊢,
        have hₑ_η, from digraph.update_data_is_edges_inv η i rtr,
        have hᵢ_η, from digraph.update_data_is_ids_inv η i rtr,
        rw [hₑ_η, hᵢ_η],
        simp,
        apply update_with_equiv_rtr_all_data_equiv,
        exact hₑ
      end

    -- The proposition, that for all input ports (`i`) in `η` the number of edges that have `i` as
    -- destination is ≤ 1.
    def has_unique_port_ins (η : graph υ) : Prop :=
      ∀ e e' : edge, (e ∈ η) → (e' ∈ η) → e ≠ e' → e.dst ≠ e'.dst
      -- Alternatively: ∀ e e' : edge, (e ∈ η) → (e' ∈ η) → e = e' ∨ e.dst ≠ e'.dst

    lemma edges_inv_unique_port_ins_inv {η η' : graph υ} :
      η.edges = η'.edges → η.has_unique_port_ins → η'.has_unique_port_ins :=
      begin
        intros hₑ hᵤ,
        unfold has_unique_port_ins,
        intros e e',
        unfold has_unique_port_ins at hᵤ,
        simp [(∈)] at hᵤ ⊢,
        rw ← hₑ,
        apply hᵤ 
      end

    lemma update_reactor_equiv (η : graph υ) (i : reactor.id) (r : reactor υ) (h : η.rtr i ≈ r) :
      (η.update_reactor i r) ≈ η :=
      begin
        unfold update_reactor,
        exact symm_of (≈) (graph.update_with_equiv_rtr_is_equiv η i r h)
      end

    lemma update_input_equiv (η : graph υ) (p : port.id) (v : option υ) :
      (η.update_input p v) ≈ η :=
      begin
        unfold update_input,
        have h : (η.data p.rtr).update_input p.prt v ≈ (η.data p.rtr), from reactor.update_input_equiv _ p.prt v,
        simp [(≈)],
        exact update_reactor_equiv _ _ _ h
      end

    lemma update_reactor_out_inv (η : graph υ) (i : reactor.id) (rtr : reactor υ) (h : rtr.output = (η.rtr i).output) :
      ∀ o, (η.update_reactor i rtr).output o = η.output o :=
      begin
        intro o,
        unfold output,
        suffices h : ((η.update_reactor i rtr).data o.rtr).output = (η.data o.rtr).output, { rw h },
        unfold update_reactor digraph.update_data,
        simp,
        rw function.update_apply,
        by_cases hᵢ : o.rtr = i,
          {
            rw [if_pos hᵢ, hᵢ],
            exact h
          },
          rw if_neg hᵢ
      end

    lemma update_input_out_inv (η : graph υ) (p : port.id) (v : option υ) :
      ∀ o, (η.update_input p v).output o = η.output o :=
      begin
        unfold update_input,
        apply update_reactor_out_inv,
        apply reactor.update_input_out_inv
      end

    lemma update_reactor_comm {i i' : reactor.id} (h : i ≠ i') (r r' : reactor υ) (η : graph υ) :
      (η.update_reactor i r).update_reactor i' r' = (η.update_reactor i' r').update_reactor i r :=
      begin
        unfold update_reactor,
        apply digraph.update_data_comm,
        exact h,
      end 

    lemma update_input_comm {i i' : port.id} (h : i ≠ i') (v v' : option υ) (η : graph υ) :
      (η.update_input i v).update_input i' v' = (η.update_input i' v').update_input i v :=
      sorry

  end graph

end network