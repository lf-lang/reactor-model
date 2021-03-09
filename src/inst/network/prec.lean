import digraph
import inst.network.graph
open reactor.ports

namespace inst
namespace network

  -- An edge in a precedence graph connects reactions.
  structure prec.graph.edge := 
    (src : reaction.id)
    (dst : reaction.id)

  -- Precedence graph edges are directed.
  instance prec.graph.digraph_edge : digraph.edge prec.graph.edge reaction.id := 
    { src := (λ e, e.src), dst := (λ e, e.dst) }

  -- Cf. inst/primitives.lean
  variables (υ : Type*) [decidable_eq υ]

  -- A precedence graph is a digraph of reactions, identified by reaction-IDs
  -- and connected by the edges define above.
  def prec.graph : Type* := digraph reaction.id (reaction υ) prec.graph.edge

  variable {υ}

  namespace prec
  namespace graph

    -- A reaction is a member of a precedence graph if the graph contains an ID that maps to it.
    instance rcn_mem : has_mem (reaction υ) (prec.graph υ) := {mem := λ rcn ρ, ∃ i, ρ.data i = rcn}

    -- The reaction in a precedence graph, that is associated with a given reaction ID.
    noncomputable def rcn (ρ : prec.graph υ) (i : reaction.id) : reaction υ :=
      ρ.data i

    -- A reaction `i` is internally dependent on `i'`, if they live in the same reactor and `i`'s
    -- priority is above `i'`'s.
    -- Note, this implies that reactions can have multiple internal dependencies, and hence a
    -- well-formed precedence graph will have an edge for each of these. This doesn't matter
    -- though, because the topological order is not affected by this.
    def internally_dependent (i i' : reaction.id) : Prop := (i.rtr = i'.rtr) ∧ (i.rcn > i'.rcn)

    -- A reaction `i` is externally dependent on `i'`, if there exists a connection from an 
    -- output-dependency of `i` to an input-dependency of `i'` in the network graph.
    def externally_dependent (i i' : reaction.id) (η : inst.network.graph υ) : Prop :=
      ∃ e : inst.network.graph.edge, (e ∈ η.edges) ∧ (e.src ∈ η.deps i role.output) ∧ (e.dst ∈ η.deps i' role.input)

    -- A well-formed precedence graph should contain edges between exactly those reactions that
    -- have a direct dependency in the corresponding network graph.
    def edges_are_well_formed_over (ρ : prec.graph υ) (η : inst.network.graph υ) : Prop :=
      ∀ e : edge, e ∈ ρ.edges ↔ (internally_dependent e.src e.dst ∨ externally_dependent e.src e.dst η)

    -- A well-formed precedence graph should contain an ID (and by extension a member) iff
    -- the ID can be used to identify a reaction in the corresponding network graph.
    def ids_are_well_formed_over (ρ : prec.graph υ) (η : inst.network.graph υ) : Prop :=
      ∀ i : reaction.id, i ∈ ρ.ids ↔ (i.rtr ∈ η.ids ∧ i.rcn ∈ (η.rtr i.rtr).priorities)
      
    -- A well-formed precedence graph's data map should return exactly those reactions that
    -- correspond to the given ID in the network graph.
    -- Originally this was formalized as: `∀ i, i ∈ ρ.ids → ρ.rcn i = η.rcn i`
    -- A consequence of stating it this way, is that precedence graphs may differ in the data that 
    -- they associated with irrelevant (`∉ ρ.ids`) reaction-IDs. This then makes it impossible to
    -- prove `wf_prec_graphs_are_eq`.
    -- It would be possible to adjust the theorem to state that all well-formed precedence graphs 
    -- are equal, excluding their `data` maps on irrelevant IDs - but that would be more work than 
    -- it's worth.
    def data_is_well_formed_over (ρ : prec.graph υ) (η : inst.network.graph υ) : Prop :=
      ∀ i, ρ.rcn i = η.rcn i

    -- A precedence graph is well formed over a given network graph, if its ids, data and edges 
    -- fulfill the properties above.
    def is_well_formed_over (ρ : prec.graph υ) (η : inst.network.graph υ) : Prop :=
      ρ.ids_are_well_formed_over   η ∧ 
      ρ.data_is_well_formed_over   η ∧ 
      ρ.edges_are_well_formed_over η 

    notation ρ `⋈` η := (ρ.is_well_formed_over η) 

    -- Two reactions are independent in a precedence graph if there are no paths between them.
    def indep (ρ : prec.graph υ) (i i' : reaction.id) : Prop := ¬(i~ρ~>i') ∧ ¬(i'~ρ~>i)

    -- Independent reactions can not live in the same reactor.
    lemma indep_rcns_neq_rtrs {η : inst.network.graph υ} {ρ : prec.graph υ} (hw : ρ ⋈ η) {i i' : reaction.id} (hₙ : i ≠ i') (hᵢ : ρ.indep i i') :
      i.rtr ≠ i'.rtr :=
      begin
        by_contradiction hc,
        simp at hc,
        by_cases hg : i.rcn > i'.rcn,
          {
            let e := {edge . src := i, dst := i'},
            have hd : internally_dependent i i', from ⟨hc, hg⟩,
            have hₑ, from (hw.right.right e).mpr (or.inl hd),
            have h_c', from digraph.has_path_from_to.direct ⟨e, hₑ, refl _⟩,
            have hᵢ', from hᵢ.left,
            contradiction
          },
          {
            by_cases hg' : i.rcn = i'.rcn,
              { have hₑ : i = i', { ext, exact hc, exact hg' }, contradiction },
              {
                simp at hg hg',
                let e := {edge . src := i', dst := i},
                have h_d : internally_dependent i' i, from ⟨symm hc, nat.lt_of_le_and_ne hg hg'⟩,
                have hₑ, from (hw.right.right e).mpr (or.inl h_d),
                have h_c', from digraph.has_path_from_to.direct ⟨e, hₑ, refl _⟩,
                have hᵢ', from hᵢ.right,
                contradiction
              }
          }
      end

  end graph
  end prec

  -- The proposition, that every well-formed precedence graph over a network is acyclic.
  def graph.is_prec_acyclic (η : inst.network.graph υ) : Prop :=
    ∀ ρ : prec.graph υ, (ρ ⋈ η) → ρ.is_acyclic
 
  namespace prec

    -- Any precedence-acyclic network graph has a wellformed precedence graph.
    -- We can prove this theorem by presenting an algorithm that generates a well-formed precedence graph.
    -- An algorithm for this is presented in [cyph20].
    theorem prec_acyc_net_graph_has_wf_prec_graph (η : inst.network.graph υ) (h : η.is_prec_acyclic) :
      ∃ ρ : prec.graph υ, ρ ⋈ η :=
      sorry

    -- All precedence graphs that are wellformed over a fixed network graph are equal.
    theorem wf_prec_graphs_are_eq {η : inst.network.graph υ} {ρ ρ' : prec.graph υ} (hw : ρ ⋈ η) (hw' : ρ' ⋈ η) :
      ρ = ρ' :=
      begin
        ext x,
          exact iff.trans (hw.left x) (iff.symm (hw'.left x)),
          { 
            funext, 
            exact eq.trans (hw.right.left x) (eq.symm (hw'.right.left x)) 
          },
          {
            rw finset.ext_iff,
            intro x,
            exact iff.trans (hw.right.right x) (iff.symm (hw'.right.right x))
          }
      end

    -- Any precedence-acyclic network graph has exactly one wellformed precedence graph.
    theorem prec_acyc_net_graph_has_exactly_one_wf_prec_graph {η : inst.network.graph υ} (h : η.is_prec_acyclic) :
      ∃! ρ : prec.graph υ, ρ ⋈ η :=
      begin
        rw exists_unique,
        obtain ⟨ρ, hₚ⟩ := classical.subtype_of_exists (prec_acyc_net_graph_has_wf_prec_graph η h),
        existsi ρ,
        split,
          exact hₚ,
          {
            intros m hₘ,
            apply wf_prec_graphs_are_eq hₘ hₚ
          }
      end

  end prec

  namespace graph
  open prec.graph

    -- Equivalent network graphs have the same well-formed precedence graphs.
    theorem equiv_wf_prec_inv {η η' : inst.network.graph υ} {ρ : prec.graph υ} (h : η' ≈ η) (hw : ρ ⋈ η) : ρ ⋈ η' :=
      begin
        unfold is_well_formed_over at hw ⊢,
        simp only [(≈)] at h,
        repeat { split },
          {
            unfold ids_are_well_formed_over at hw ⊢,
            intro x,
            rw ←h.right.left at hw,
            simp only [symm (h.right.right x.rtr).left, hw.left x]
          },
          {
            unfold data_is_well_formed_over rcn at hw ⊢,
            intro x,
            simp only [(h.right.right x.rtr).right, hw.right.left x]
          },
          {
            unfold edges_are_well_formed_over externally_dependent at hw ⊢,
            intro x,
            simp only [h.left, deps, rcn, (h.right.right x.src.rtr).right, (h.right.right x.dst.rtr).right, hw.right.right x]
          }
      end

    -- Equivalent network graphs have the same precedence-acyclicity.
    theorem equiv_prec_acyc_inv {η η' : inst.network.graph υ} (hₑ : η ≈ η') (hₚ : η.is_prec_acyclic) :
      η'.is_prec_acyclic :=
      begin
        unfold inst.network.graph.is_prec_acyclic at hₚ ⊢,
        let ρ := classical.subtype_of_exists (prec.prec_acyc_net_graph_has_wf_prec_graph η hₚ),
        intros ρ' hw',
        have hₐ, from hₚ ρ ρ.property,
        suffices h : (ρ : prec.graph υ).edges = ρ'.edges, from digraph.eq_edges_acyclic h hₐ,
        have hw'', from equiv_wf_prec_inv (equiv_symm hₑ) ρ.property,
        simp [prec.wf_prec_graphs_are_eq hw' hw'']
      end

    -- Use run_out_diff_sub_dₒ?
    lemma index_diff_sub_dₒ (η : graph υ) (i : reaction.id) : 
      (((η.run_local i).rtr i.rtr).prts role.output).index_diff ((η.rtr i.rtr).prts role.output) ⊆ (η.rcn i).deps role.output :=
      sorry 

    -- (1) p is in the difflist of (run i)   [by hₚ]
    -- (2) -> p is an output dependency of i [by run_out_diff_sub_dₒ]
    -- 
    -- (3) e.src = p                         [by hₑ]
    -- (4) -> e.src is an output dep of i    [by 2 & 3]
    --
    -- (5) i' does not depend on i           [by extension of hᵢ] (∃ (o) (j), (i-η->o) ∧ {inst.network.graph.edge . src := o, dst := j} ∈ η.edges ∧ (j-η->i'))
    -- (6) -> for all o and j, not all of the following are true:
    --      (i) o depends on i
    --      (ii) there's an edge from o to j 
    --      (iii) i' depends on j
    --
    -- (7) (i) is true by virtue of (4)
    -- (8) -> (ii) or (iii) must be false
    --
    -- by cases:
    --   * if (ii) is true, then (iii) isnt
    --      -> for all edges from o to j, the edge's destination j isnt a dependecy of i'
    --      -> this holds for e as well
    --   * if (iii) is true, then (ii) isnt,
    --      -> there does not exist an edge that ends in a j such that j is a dependency of i',
    --      -> e does not end in a dependency of i'
    lemma run_local_index_diff_eₒ {η : inst.network.graph υ} (hᵤ : η.has_unique_port_ins) {ρ : prec.graph υ} (hw : ρ.is_well_formed_over η) {i i' : reaction.id} (hᵢ : ¬(i~ρ~>i')) (hₙ : i.rtr ≠ i'.rtr) :
      ∀ (p ∈ ((η.run_local i).index_diff η i.rtr role.output).val.to_list) (e : inst.network.graph.edge), (e ∈ (η.run_local i).eₒ p) → e.dst ∉ ((η.run_local i).deps i' role.input) ∧ (e.src ∉ (η.run_local i).deps i' role.output) :=
      begin
         -- have hq, from inst.network.graph.run_local_equiv η i,
        -- unfold inst.network.graph.deps inst.network.graph.rcn,
        -- rw [(hq.right.right _).right, ←inst.network.graph.rcn],
        -- repeat { rw ←inst.network.graph.deps },
        --
        -- have hd, from prec.graph.indep_rcns_not_ext_dep hw hₙ hᵢ,
        -- rw externally_dependent at hd,
        -- simp [port_depends_on_reaction, reaction_depends_on_port] at hd,
        -- by_contradiction,
        -- simp at h,

        intros p hₚ e hₑ,
        rw [multiset.mem_to_list, ←finset.mem_def, index_diff, finset.mem_image] at hₚ,
        obtain ⟨p_prt, h_p_prt, H⟩ := hₚ,
        /-have HH, from index_diff_sub_dₒ η i,
        simp only [(⊆)] at HH,
        replace h_p_prt := HH h_p_prt, -- (2)
        simp only [eₒ, finset.mem_filter] at hₑ, -- (3)
        -/

        /-
        have H : i ≠ i', {
              by_contradiction,
              simp at h,
              cases i,
              cases i',
              rw h at hₙ,
              simp only [rtr] at hₙ,
              contradiction,
            },
        -/

        split,
          {
            sorry
          },
          {
            unfold deps,
            rw finset.mem_image at ⊢,
            cases p,
            injection H, -- hₑ & h_1
            rw ←h_1 at hₑ,
            by_contradiction,
            obtain ⟨_, _, H'⟩ := h,
            simp only [eₒ, finset.mem_filter] at hₑ,
            have HH, from hₑ.right,
            rw HH at H',
            injection H',
            have HHH, from ne.symm hₙ,
            contradiction,
          }
      end

  end graph

end network
end inst
