import data.rel
import graphs.digraph
import reactor.network.basic

namespace reactor 
namespace network
namespace «precedence» 

  variables {c : ℕ} (n : network c)

  namespace graph

    structure reaction_id := 
      (rtr : { i // i ∈ n.graph.ids })
      (rcn : fin (n.graph.data rtr).nᵣ)

    instance dec_eq_rcn_id : decidable_eq (reaction_id n) := sorry

    structure edge := 
      (src : reaction_id n)
      (dst : reaction_id n)

    instance digraph_edge {n : network c} : digraph.edge (graph.edge n) (reaction_id n) := 
      { src := (λ e, e.src), dst := (λ e, e.dst) }

  end graph

  def graph := digraph (graph.reaction_id n) reaction (λ _ _, graph.edge n)

  namespace graph

    private def rtr_id_to_rcn_ids (n : network c) (rtr_id : {i // i ∈ n.graph.ids}) : finset (reaction_id n) :=
      let internal_rcn_id := fin (n.graph.data rtr_id).nᵣ in
      let internal_rcn_ids := fintype.elems internal_rcn_id in
      let completion_fun : internal_rcn_id → reaction_id n := λ i, {rtr := rtr_id, rcn := i} in
      internal_rcn_ids.map {to_fun := completion_fun, inj' := sorry}

    private def rtr_id_to_rcn_edges (n : network c) (rtr_id : {i // i ∈ n.graph.ids}) : finset (edge n) :=
      let rcn_count := (n.graph.data rtr_id).nᵣ in
        if h : rcn_count > 1
        then 
          let internal_rcn_id := fin rcn_count in
          let internal_rcn_ids := fintype.elems internal_rcn_id in
          let connect_fun : { x : internal_rcn_id // x ≠ 0 } → edge n := λ i, 
            {src := {rtr := rtr_id, rcn := i.val.pred i.property}, dst := {rtr := rtr_id, rcn := i.val}} in
          let ids_ne_zero := internal_rcn_ids.erase 0 in
          let x := ids_ne_zero.attach
            .map {
              to_fun := (λ i : {x // x ∈ ids_ne_zero}, let h : i ≠ 0 := finset.ne_of_mem_erase i.property in ⟨i.val, h⟩ ), 
              inj' := sorry
            }
            in sorry
            -- .map {to_fun := connect_fun, inj' := sorry}
        else ∅ 

    -- This is basically the "precedence function" from definition 11.
    def mk (n : network c) : precedence.graph n :=
      let nested_rcn_ids : finset (finset (reaction_id n)) := n.graph.ids.attach.map {to_fun := rtr_id_to_rcn_ids n, inj' := sorry} in
      let rcn_ids : finset (reaction_id n) := finset.fold (∪) ∅ id nested_rcn_ids in -- These will be the vertices.
      let data_map : {x // x ∈ rcn_ids} → reaction := λ i : {x // x ∈ rcn_ids}, (n.graph.data i.val.rtr).reactions i.val.rcn in
      let intra_rtr_edges : finset (finset (edge n)) := n.graph.ids.attach.map {to_fun := rtr_id_to_rcn_edges n, inj' := sorry} in
      let extra_rtr_edges : finset (finset (edge n)) := sorry in
      let edges : finset (edge n) := finset.fold (∪) ∅ id (intra_rtr_edges ∪ extra_rtr_edges) in
      {ids := rcn_ids, data := data_map, edges := edges}

    theorem correctness (n : network c) : /-Instance of-/ Prop := 
      sorry
      -- For all reactions that are implicitly connected in a certain way in the network,
      -- they need to have the analogous explicit connections in the precedence graph.

    -- Define "correctness".
    -- Have theorem that a correct prec. graph exists for every network.
    --    * keep this sorryed
    --    * perhaps the constructive path is easier here

  end graph

end «precedence»
end network
end reactor