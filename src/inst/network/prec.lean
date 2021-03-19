import lgraph
import inst.network.graph
open reactor.ports

namespace inst
namespace network

  -- An edge in a precedence graph connects reactions.
  structure prec.graph.edge := 
    (src : reaction.id)
    (dst : reaction.id)

  -- Precedence graph edges are directed.
  instance prec.graph.lgraph_edge : lgraph.edge prec.graph.edge reaction.id := 
    { src := (λ e, e.src), dst := (λ e, e.dst) }

  -- Cf. inst/primitives.lean
  variables (υ : Type*) [decidable_eq υ]

  -- A precedence graph is an L-graph of reactions, identified by reaction-IDs
  -- and connected by the edges define above.
  def prec.graph : Type* := lgraph reaction.id (reaction υ) prec.graph.edge

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
            have h_c', from lgraph.has_path_from_to.direct ⟨e, hₑ, refl _⟩,
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
                have h_c', from lgraph.has_path_from_to.direct ⟨e, hₑ, refl _⟩,
                have hᵢ', from hᵢ.right,
                contradiction
              }
          }
      end

    -- If a reaction `i'` does not depend on another reaction `i`, then it is neither internally nor externally dependent on `i`.
    lemma no_path_no_dep {η : inst.network.graph υ} {ρ : prec.graph υ} (h : ρ ⋈ η) {i i' : reaction.id} (hᵢ : ¬(i~ρ~>i')) :
      ¬(internally_dependent i i') ∧ ¬(externally_dependent i i' η) :=
      begin 
        let e := {edge . src := i, dst := i'},
        unfold is_well_formed_over edges_are_well_formed_over at h,
        replace h := h.right.right e,
        have hₑ' : e ∉ ρ.edges, {
          by_contradiction,
          have, from lgraph.has_path_from_to.direct ⟨e, h, refl _⟩,
          contradiction
        },
        replace h := (not_iff_not_of_iff h).mp hₑ',
        exact not_or_distrib.mp h
      end

    -- If there is no path from a reaction `i` to a reaction `i'`, then none of the edges coming out of `i`'s output dependencies have 
    -- a dependency relationship with `i'`.
    -- This lemma is somewhat specific, as it is required for `inst.network.graph.run_reaction_comm`.
    lemma no_path_no_eₒ_dep {η : inst.network.graph υ} {ρ : prec.graph υ} (hw : ρ ⋈ η) {i i' : reaction.id} (hᵢ : ¬(i~ρ~>i')) (hₙ : i.rtr ≠ i'.rtr) {ps : finset port.id} (hₛ : ps ⊆ η.deps i role.output) :
      ∀ (p ∈ ps) (e : inst.network.graph.edge), (e ∈ η.eₒ p) → e.dst ∉ (η.deps i' role.input) ∧ (e.src ∉ η.deps i' role.output) :=
      begin
        intros p hₚ e hₑ,
        rw graph.mem_eₒ at hₑ,
        simp only [(⊆)] at hₛ,
        split,
          {
            have hd, from (no_path_no_dep hw hᵢ).right,
            rw [externally_dependent, not_exists] at hd,
            replace hd := hd e,
            repeat { rw not_and_distrib at hd },
            replace hd := hd.resolve_left (not_not_intro hₑ.left),
            rw ←hₑ.right at hₚ,
            exact hd.resolve_left (not_not_intro (hₛ hₚ))
          },
          {
            simp only [graph.deps, finset.mem_image, not_exists] at hₛ ⊢,
            obtain ⟨x, hₓ, hₚ⟩ := hₛ hₚ,
            intros y hy,
            rw [hₑ.right, ←hₚ],
            by_contradiction,
            injection h,
            replace h := eq.symm h_1,
            contradiction
          }
      end

  end graph
  end prec

  -- The proposition, that every well-formed precedence graph over a network is acyclic.
  def graph.is_prec_acyclic (η : inst.network.graph υ) : Prop :=
    ∀ ρ : prec.graph υ, (ρ ⋈ η) → ρ.is_acyclic
 
  -- All precedence graphs that are wellformed over a fixed network graph are equal.
  theorem prec.wf_prec_graphs_are_eq {η : inst.network.graph υ} {ρ ρ' : prec.graph υ} (hw : ρ ⋈ η) (hw' : ρ' ⋈ η) :
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

  namespace graph
  open prec.graph

    -- Equivalent network graphs have the same well-formed precedence graphs.
    theorem equiv_wf_prec_inv {η η' : graph υ} {ρ : prec.graph υ} (h : η' ≈ η) (hw : ρ ⋈ η) : ρ ⋈ η' :=
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
    theorem equiv_prec_acyc_inv {η η' : graph υ} (hq : η ≈ η') (hₚ : η.is_prec_acyclic) :
      η'.is_prec_acyclic :=
      begin
        unfold is_prec_acyclic at hₚ ⊢,
        intros ρ hw,
        exact hₚ ρ (equiv_wf_prec_inv hq hw)
      end    

  end graph

end network
end inst
