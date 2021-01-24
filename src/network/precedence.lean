import digraph
import network.graph
import network.ids

namespace network
namespace «precedence» 

  namespace graph

    structure edge := 
      (src : reaction.id)
      (dst : reaction.id)

    instance digraph_edge : digraph.edge graph.edge reaction.id := 
      { src := (λ e, e.src), dst := (λ e, e.dst) }

  end graph

  def graph := digraph reaction.id reaction precedence.graph.edge

  instance : has_mem reaction precedence.graph := {mem := λ r g, ∃ i, g.data i = r}

  namespace graph

    -- The reaction contained in a precedence graph, that is associated with a given reaction ID.
    noncomputable def rcn (ρ : precedence.graph) (i : reaction.id) : reaction :=
      ρ.data i

    def port_depends_on_reaction (p : port.id) (r : reaction.id) (η : network.graph) : Prop :=
      p.rtr = r.rtr ∧ p.prt ∈ (η.rcn r).dₒ 

    notation r-n->p := port_depends_on_reaction p r n

    def reaction_depends_on_port (r : reaction.id) (p : port.id) (η : network.graph) : Prop :=
      p.rtr = r.rtr ∧ p.prt ∈ (η.rcn r).dᵢ

    notation p-n->r := reaction_depends_on_port r p n

    -- A reaction `r` is internally dependent on `r'` if they live in the same reactor and `r`'s
    -- priority is above `r'`'s.
    --
    -- Note, this implies that reactions can have multiple internal dependencies, and hence a
    -- well-formed precedence graph will have an edge for each of these. This doesn't matter
    -- though, because the topological order is not affected by this.
    def internally_dependent (r r' : reaction.id) : Prop :=
      r.rtr = r'.rtr ∧ r.rcn > r'.rcn

    -- A reaction `r` is externally dependent on `r'` there is a connection from an output-port of
    -- `r` to an input-port of `r'`.
    def externally_dependent (r r' : reaction.id) (η : network.graph) : Prop :=
      ∃ (o) (i), (r-η->o) ∧ {network.graph.edge . src := o, dst := i} ∈ η.edges ∧ (i-η->r')

    -- A well-formed precedence graph should contain edges between exactly those reactions that
    -- have a direct dependency in the corresponding network graph.
    def edges_are_well_formed_over (ρ : precedence.graph) (η : network.graph) : Prop :=
      ∀ e : graph.edge, e ∈ ρ.edges ↔ (internally_dependent e.src e.dst ∨ externally_dependent e.src e.dst η)

    -- A well-formed precedence graph should contain an ID (and by extension a member) iff
    -- the ID can be used to identify a reaction in the corresponding network graph.
    def ids_are_well_formed_over (ρ : precedence.graph) (η : network.graph) : Prop :=
      ∀ i : reaction.id, i ∈ ρ.ids ↔ (i.rtr ∈ η.ids ∧ i.rcn ∈ (η.rtr i.rtr).priorities)
      
    -- A well-formed precedence graph's data map should return exactly those reactions that
    -- correspond to the given ID in the network graph.
    --
    -- Originally this was stated as: `∀ i ∈ ρ.ids, ρ.rcn i = η.rcn i`
    -- The consequence of stating it this way though, is that `all_wf_prec_graphs_are_eq` is false,
    -- since two precedence graphs may differ on `ρ.data i` for `i ∉ ρ.ids`. It would be possible
    -- to adjust the theorem to state that all well-formed precedence graphs are equal, excluding
    -- their `data` maps on non-important input - but that would be more work than it's worth.
    def data_is_well_formed_over (ρ : precedence.graph) (η : network.graph) : Prop :=
      ∀ i, ρ.rcn i = η.rcn i

    def is_well_formed_over (ρ : precedence.graph) (η : network.graph) : Prop :=
      ρ.ids_are_well_formed_over   η ∧ 
      ρ.data_is_well_formed_over   η ∧ 
      ρ.edges_are_well_formed_over η 

    lemma indep_rcns_neq_rtrs {η : network.graph} {ρ : precedence.graph} (h : ρ.is_well_formed_over η) {i i' : reaction.id} :
      i ≠ i' → ¬(i~ρ~>i') → ¬(i'~ρ~>i) → i.rtr ≠ i'.rtr :=
      begin
        intros hᵢ hₚ hₚ',
        by_contradiction h_c,
        simp at h_c,
        by_cases h_g : i.rcn > i'.rcn,
          {
            let e := {graph.edge . src := i, dst := i'},
            have h_d : internally_dependent i i', from ⟨h_c, h_g⟩,
            have hₑ, from (h.right.right e).mpr (or.inl h_d),
            have h_c', from digraph.has_path_from_to.direct ⟨e, hₑ, refl _⟩,
            contradiction,
          },
          {
            by_cases h_g' : i.rcn = i'.rcn,
              {
                have hₑ : i = i', { ext, exact h_c, exact h_g' },
                contradiction
              },
              {
                simp at h_g h_g',
                let e := {graph.edge . src := i', dst := i},
                have h_d : internally_dependent i' i, from ⟨symm h_c, nat.lt_of_le_and_ne h_g h_g'⟩,
                have hₑ, from (h.right.right e).mpr (or.inl h_d),
                have h_c', from digraph.has_path_from_to.direct ⟨e, hₑ, refl _⟩,
                contradiction,
              }
          }
      end

  end graph

end «precedence»
end network

-- The proposition, that every well-formed precedence graph over a network is acyclic.
def network.graph.is_prec_acyclic (η : network.graph) : Prop :=
  ∀ ρ : network.precedence.graph, ρ.is_well_formed_over η → ρ.is_acyclic

namespace network
namespace «precedence» 

  theorem any_acyc_net_graph_has_wf_prec_graph (η : network.graph) (h : η.is_prec_acyclic) :
    ∃ ρ : precedence.graph, ρ.is_well_formed_over η :=
    sorry

  lemma wf_prec_graphs_eq_ids (η : network.graph) (ρ ρ' : precedence.graph) :
    ρ.is_well_formed_over η → ρ'.is_well_formed_over η → ρ.ids = ρ'.ids :=
    begin 
      intros h_wf h_wf',
      have h_i  :  ρ.ids_are_well_formed_over η, from h_wf.left,
      have h_i' : ρ'.ids_are_well_formed_over η, from h_wf'.left,
      rw graph.ids_are_well_formed_over at h_i h_i',
      suffices h : ∀ i, i ∈ ρ.ids ↔ i ∈ ρ'.ids, from finset.ext_iff.mpr h,
      intro i,
      exact iff.trans (h_i i) (iff.symm (h_i' i))
    end

  lemma wf_prec_graphs_eq_data (η : network.graph) (ρ ρ' : precedence.graph) :
    ρ.is_well_formed_over η → ρ'.is_well_formed_over η → ρ.data = ρ'.data :=
    begin
      intros h_wf h_wf',
      have h_d  :  ρ.data_is_well_formed_over η, from h_wf.right.left,
      have h_d' : ρ'.data_is_well_formed_over η, from h_wf'.right.left,
      rw graph.data_is_well_formed_over at h_d h_d',
      suffices h : ∀ i, ρ.data i = ρ'.data i, from funext h,
      intro i,
      exact eq.trans (h_d i) (eq.symm (h_d' i))
    end

  lemma wf_prec_graphs_eq_edges (η : network.graph) (ρ ρ' : precedence.graph) :
    ρ.is_well_formed_over η → ρ'.is_well_formed_over η → ρ.edges = ρ'.edges :=
    begin
      intros h_wf h_wf',
      have h_e  :  ρ.edges_are_well_formed_over η, from h_wf.right.right,
      have h_e' : ρ'.edges_are_well_formed_over η, from h_wf'.right.right,
      rw graph.edges_are_well_formed_over at h_e h_e',
      suffices h : ∀ e, e ∈ ρ.edges ↔ e ∈ ρ'.edges, from finset.ext_iff.mpr h,
      intro e,
      exact iff.trans (h_e e) (iff.symm (h_e' e)),
    end

  theorem all_wf_prec_graphs_are_eq (η : network.graph) (ρ ρ' : precedence.graph) :
    ρ.is_well_formed_over η → ρ'.is_well_formed_over η → ρ = ρ' :=
    begin
      intros h_wf h_wf',
      have h_i : ρ.ids   = ρ'.ids,   from wf_prec_graphs_eq_ids   η ρ ρ' h_wf h_wf',
      have h_d : ρ.data  = ρ'.data,  from wf_prec_graphs_eq_data  η ρ ρ' h_wf h_wf',
      have h_e : ρ.edges = ρ'.edges, from wf_prec_graphs_eq_edges η ρ ρ' h_wf h_wf',
      ext,
        apply finset.ext_iff.mp h_i,
        exact congr_fun h_d x,
        apply finset.ext_iff.mp h_e
    end

  theorem any_acyc_net_graph_has_exactly_one_wf_prec_graph (η : network.graph) (h : η.is_prec_acyclic) :
    ∃! ρ : precedence.graph, ρ.is_well_formed_over η :=
    begin
      rw exists_unique,
      let ρ := (any_acyc_net_graph_has_wf_prec_graph η h).some,
      have hₚ, from (any_acyc_net_graph_has_wf_prec_graph η h).some_spec,
      apply exists.intro,
        {
          apply and.intro,
            exact hₚ,
            {
              intros m hₘ,
              apply all_wf_prec_graphs_are_eq η m ρ hₘ hₚ
            }
        }
    end

end «precedence»
end network

open network.precedence.graph

lemma network.graph.equiv_eq_wf_prec_edges {η η' : network.graph} {ρ ρ' : network.precedence.graph} :
  η ≈ η' → ρ.is_well_formed_over η → ρ'.is_well_formed_over η' → ρ.edges = ρ'.edges :=
  begin
    intros hₑ_η h_wf h_wf',
    have hₑ, from h_wf.right.right,
    have hₑ', from h_wf'.right.right,
    unfold edges_are_well_formed_over at hₑ hₑ',
    suffices h : ∀ e, e ∈ ρ.edges ↔ e ∈ ρ'.edges, from finset.ext_iff.mpr h,
    intro e,
    replace hₑ := hₑ e,
    replace hₑ' := hₑ' e,
    suffices h : externally_dependent e.src e.dst η ↔ externally_dependent e.src e.dst η', {
      rw h at hₑ,
      exact iff.trans hₑ (iff.symm hₑ')
    },
    simp only [(≈)] at hₑ_η,
    unfold externally_dependent,
    rw hₑ_η.left,
    have hᵣ_eq : ∀ (x : reactor.id), (η.data x).reactions = (η'.data x).reactions, {
      have hᵣ, from hₑ_η.right,
      rw forall_and_distrib at hᵣ,
      exact hᵣ.right.right
    },
    have hₒ : ∀ o, (port_depends_on_reaction o e.src η) ↔ (port_depends_on_reaction o e.src η'), {
      unfold port_depends_on_reaction,
      intro o,
      have h_d : (η.rcn e.src).dₒ = (η'.rcn e.src).dₒ, {
        unfold network.graph.rcn,
        rw hᵣ_eq e.src.rtr
      },
      rw h_d
    },
    have hᵢ : ∀ i, (reaction_depends_on_port e.dst i η) ↔ (reaction_depends_on_port e.dst i η'), {
      unfold reaction_depends_on_port,
      intro i,
      have h_d : (η.rcn e.dst).dᵢ = (η'.rcn e.dst).dᵢ, {
        unfold network.graph.rcn,
        rw hᵣ_eq e.dst.rtr
      },
      rw h_d
    },
    finish
  end

theorem network.graph.equiv_wf {η η' : network.graph} {ρ : network.precedence.graph} :
  η' ≈ η → ρ.is_well_formed_over η → ρ.is_well_formed_over η' :=
  begin
    intros h h_wf,
    unfold network.precedence.graph.is_well_formed_over,
    simp [(≈)] at h,
    unfold ids_are_well_formed_over,
    sorry,
  end

theorem network.graph.equiv_prec_acyc_inv {η η' : network.graph} :
  η ≈ η' → η.is_prec_acyclic → η'.is_prec_acyclic :=
  begin
    intros hₑ hₚ,
    unfold network.graph.is_prec_acyclic at hₚ ⊢,
    let ρ := classical.subtype_of_exists (network.precedence.any_acyc_net_graph_has_wf_prec_graph η hₚ),
    intros ρ' h_wf',
    have hₐ, from hₚ ρ ρ.property,
    suffices h : (ρ : network.precedence.graph).edges = ρ'.edges, from digraph.edges_inv_acyclic_inv h hₐ,
    exact network.graph.equiv_eq_wf_prec_edges hₑ ρ.property h_wf',
  end