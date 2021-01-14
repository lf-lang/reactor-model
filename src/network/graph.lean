import digraph
import reactor
import network.ids

namespace network

  namespace graph
    
    structure edge :=
      (src : port.id)
      (dst : port.id)

    instance digraph_edge : digraph.edge graph.edge reactor.id := 
      { src := (λ e, e.src.rtr), dst := (λ e, e.dst.rtr) }

  end graph

  def graph := digraph reactor.id reactor graph.edge

  namespace graph

    @[reducible]
    instance mem : has_mem reactor graph := {mem := λ d g, ∃ i, g.data i = d}

    @[reducible]
    instance equiv : has_equiv graph := ⟨λ η η', η.edges = η'.edges ∧ η.ids = η'.ids ∧ ∀ i, (η.data i) ≈ (η'.data i)⟩

    -- The reactor contained in a network graph, that is associated with a given reaction ID.
    noncomputable def rtr (η : network.graph) (i : reaction.id) : reactor :=
      η.data i.rtr

    -- The reaction contained in a network graph, that is associated with a given reaction ID.
    noncomputable def rcn (η : network.graph) (i : reaction.id) : reaction :=
      (η.data i.rtr).reactions i.rcn

    -- Updating a network graph with an equivalent reactor keeps their `data` equivalent.
    lemma update_with_equiv_rtr_all_data_equiv {η : network.graph} (i : reactor.id) (rtr : reactor) :
      η.data i ≈ rtr → ∀ r, η.data r ≈ (η.update_data i rtr).data r :=
      begin
        intros hₑ r,
        simp at hₑ,
        unfold digraph.update_data,
        by_cases (r = i)
          ; finish
      end

    -- Updating a network graph with an equivalent reactor produces an equivalent network graph.
    theorem update_with_equiv_rtr_is_equiv (η : network.graph) (i : reactor.id) (rtr : reactor) :
      η.data i ≈ rtr → η ≈ η.update_data i rtr :=
      begin
        intro hₑ,
        simp at hₑ ⊢,
        have hₑ_η, from digraph.update_data_is_edges_inv η i rtr,
        have hᵢ_η, from digraph.update_data_is_ids_inv η i rtr,
        rw [hₑ_η, hᵢ_η],
        simp,
        apply update_with_equiv_rtr_all_data_equiv,
        exact hₑ
      end

    -- The proposition, that for all input ports (`i`) in `η` the number of edges that have `i` as
    -- destination is ≤ 1.
    def has_unique_port_ins (η : network.graph) : Prop :=
      ∀ i, (η.edges.filter (λ e', graph.edge.dst e' = i)).card ≤ 1

    lemma edges_inv_unique_port_ins_inv {η η' : network.graph} :
      η.edges = η'.edges → η.has_unique_port_ins → η'.has_unique_port_ins :=
      begin
        intros hₑ hᵤ,
        unfold has_unique_port_ins,
        intro i,
        rw ← hₑ,
        apply hᵤ
      end

    instance edge.has_le : has_le edge := ⟨λ l r, if l.src = r.src then l.dst ≤ r.dst else l.dst ≤ r.dst⟩
    instance edge.is_trans : is_trans edge has_le.le := sorry
    instance edge.is_antisymm : is_antisymm edge has_le.le := sorry
    instance edge.is_total : is_total edge has_le.le := sorry

  end graph

end network