import digraph
import inst.network.graph
open reactor.ports

namespace prec.graph

  structure edge := 
    (src : reaction.id)
    (dst : reaction.id)

  instance digraph_edge : digraph.edge edge reaction.id := 
    { src := (λ e, e.src), dst := (λ e, e.dst) }

end prec.graph

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

def prec.graph : Type* := digraph reaction.id (reaction υ) prec.graph.edge

variable {υ}

namespace prec.graph

  @[reducible]
  instance rcn_mem : has_mem (reaction υ) (prec.graph υ) := {mem := λ r g, ∃ i, g.data i = r}

  -- The reaction contained in a precedence graph, that is associated with a given reaction ID.
  noncomputable def rcn (ρ : prec.graph υ) (i : reaction.id) : reaction υ :=
    ρ.data i

  def port_depends_on_reaction (p : port.id) (r : reaction.id) (η : inst.network.graph υ) : Prop :=
    p.rtr = r.rtr ∧ p.prt ∈ (η.rcn r).dₒ 

  notation r-n->p := port_depends_on_reaction p r n

  def reaction_depends_on_port (r : reaction.id) (p : port.id) (η : inst.network.graph υ) : Prop :=
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
  def externally_dependent (r r' : reaction.id) (η : inst.network.graph υ) : Prop :=
    ∃ (o) (i), (r-η->o) ∧ {inst.network.graph.edge . src := o, dst := i} ∈ η.edges ∧ (i-η->r')

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
  --
  -- Originally this was stated as: `∀ i ∈ ρ.ids, ρ.rcn i = η.rcn i`
  -- The consequence of stating it this way though, is that `all_wf_prec_graphs_are_eq` is false,
  -- since two precedence graphs may differ on `ρ.data i` for `i ∉ ρ.ids`. It would be possible
  -- to adjust the theorem to state that all well-formed precedence graphs are equal, excluding
  -- their `data` maps on non-important input - but that would be more work than it's worth.
  def data_is_well_formed_over (ρ : prec.graph υ) (η : inst.network.graph υ) : Prop :=
    ∀ i, ρ.rcn i = η.rcn i

  def is_well_formed_over (ρ : prec.graph υ) (η : inst.network.graph υ) : Prop :=
    ρ.ids_are_well_formed_over   η ∧ 
    ρ.data_is_well_formed_over   η ∧ 
    ρ.edges_are_well_formed_over η 

  lemma indep_rcns_neq_rtrs {η : inst.network.graph υ} {ρ : prec.graph υ} (h : ρ.is_well_formed_over η) {i i' : reaction.id} :
    i ≠ i' → ¬(i~ρ~>i') → ¬(i'~ρ~>i) → i.rtr ≠ i'.rtr :=
    begin
      intros hᵢ hₚ hₚ',
      by_contradiction h_c,
      simp at h_c,
      by_cases h_g : i.rcn > i'.rcn,
        {
          let e := {edge . src := i, dst := i'},
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
              let e := {edge . src := i', dst := i},
              have h_d : internally_dependent i' i, from ⟨symm h_c, nat.lt_of_le_and_ne h_g h_g'⟩,
              have hₑ, from (h.right.right e).mpr (or.inl h_d),
              have h_c', from digraph.has_path_from_to.direct ⟨e, hₑ, refl _⟩,
              contradiction,
            }
        }
    end

  -- If two reactions `i` and `i'` are independent, then none of `i`'s antidependencies (output ports)
  -- have a connection any of `i'`'s dependencies (input ports).
  lemma indep_rcns_not_ext_dep {η : inst.network.graph υ} {ρ : prec.graph υ} (h : ρ.is_well_formed_over η) {i i' : reaction.id} :
    i ≠ i' → ¬(i~ρ~>i') → ¬(externally_dependent i i' η) :=
    begin 
      intros hₙ hₚ,
      unfold externally_dependent,
      simp,
      intros x hₓ x' hₓ',
      unfold reaction_depends_on_port,
      simp,
      intro hₑ,
      by_contradiction h_c,
      have h_d : x'-η->i', from ⟨hₑ, h_c⟩,
      have h_e : externally_dependent i i' η, from ⟨x, x', hₓ, hₓ', h_d⟩,
      have h_c', from (h.2.2 {edge . src := i, dst := i'}).mpr (or.inr h_e),
      have hₑ' : ρ.has_edge_from_to i i', from ⟨_, h_c', refl _⟩,
      have hₚ' : i~ρ~>i', from digraph.has_path_from_to.direct hₑ',
      contradiction
    end

end prec.graph

-- The proposition, that every well-formed precedence graph over a network is acyclic.
def inst.network.graph.is_prec_acyclic (η : inst.network.graph υ) : Prop :=
  ∀ ρ : prec.graph υ, ρ.is_well_formed_over η → ρ.is_acyclic

  namespace prec

  theorem any_acyc_net_graph_has_wf_prec_graph (η : inst.network.graph υ) (h : η.is_prec_acyclic) :
    ∃ ρ : prec.graph υ, ρ.is_well_formed_over η :=
    sorry

  lemma wf_prec_graphs_eq_ids (η : inst.network.graph υ) (ρ ρ' : prec.graph υ) :
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

  lemma wf_prec_graphs_eq_data (η : inst.network.graph υ) (ρ ρ' : prec.graph υ) :
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

  lemma wf_prec_graphs_eq_edges (η : inst.network.graph υ) (ρ ρ' : prec.graph υ) :
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

  theorem all_wf_prec_graphs_are_eq (η : inst.network.graph υ) (ρ ρ' : prec.graph υ) :
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

  theorem any_acyc_net_graph_has_exactly_one_wf_prec_graph (η : inst.network.graph υ) (h : η.is_prec_acyclic) :
    ∃! ρ : prec.graph υ, ρ.is_well_formed_over η :=
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

end prec

open prec.graph

lemma network.graph.equiv_eq_wf_prec_edges {η η' : inst.network.graph υ} {ρ ρ' : prec.graph υ} :
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
        unfold inst.network.graph.rcn inst.network.graph.rtr,
        rw hᵣ_eq e.src.rtr
      },
      rw h_d
    },
    have hᵢ : ∀ i, (reaction_depends_on_port e.dst i η) ↔ (reaction_depends_on_port e.dst i η'), {
      unfold reaction_depends_on_port,
      intro i,
      have h_d : (η.rcn e.dst).dᵢ = (η'.rcn e.dst).dᵢ, {
        unfold inst.network.graph.rcn inst.network.graph.rtr,
        rw hᵣ_eq e.dst.rtr
      },
      rw h_d
    },
    finish
  end

theorem network.graph.equiv_wf {η η' : inst.network.graph υ} {ρ : prec.graph υ} :
  η' ≈ η → ρ.is_well_formed_over η → ρ.is_well_formed_over η' :=
  begin
    intros h h_wf,
    unfold prec.graph.is_well_formed_over at h_wf ⊢,
    simp [(≈)] at h,
    repeat { split },
      {
        unfold ids_are_well_formed_over at h_wf ⊢,
        rw ←h.2.1 at h_wf,
        intro x,
        have h_r, from h.2.2 x.rtr,
        have h_wf', from (h_wf.1 x),
        rw ←h_r.1 at h_wf',
        exact h_wf'
      },
      {
        unfold data_is_well_formed_over at h_wf ⊢,
        intro x,
        sorry
      },
      {
        unfold edges_are_well_formed_over at h_wf ⊢,
        intro x,
        sorry
      } 
  end

theorem inst.network.graph.equiv_prec_acyc_inv {η η' : inst.network.graph υ} :
  η ≈ η' → η.is_prec_acyclic → η'.is_prec_acyclic :=
  begin
    intros hₑ hₚ,
    unfold inst.network.graph.is_prec_acyclic at hₚ ⊢,
    let ρ := classical.subtype_of_exists (prec.any_acyc_net_graph_has_wf_prec_graph η hₚ),
    intros ρ' h_wf',
    have hₐ, from hₚ ρ ρ.property,
    suffices h : (ρ : prec.graph υ).edges = ρ'.edges, from digraph.eq_edges_acyclic h hₐ,
    exact network.graph.equiv_eq_wf_prec_edges hₑ ρ.property h_wf',
  end

lemma inst.network.graph.run_local_index_diff_eₒ {η : inst.network.graph υ} (hᵤ : η.has_unique_port_ins) {ρ : prec.graph υ} (hw : ρ.is_well_formed_over η) {i i' : reaction.id} (hᵢ : ¬(i~ρ~>i')) (hₙ : i ≠ i') :
  ∀ (p ∈ ((η.run_local i).index_diff η i.rtr role.output).val.to_list) (e : inst.network.graph.edge), (e ∈ (η.run_local i ).eₒ p) → e.dst ∉ ((η.run_local i).deps i' role.input) ∧ (e.src ∉ (η.run_local i).deps i' role.output) :=
  begin
    intros p hₚ e hₑ,
    have hd, from prec.graph.indep_rcns_not_ext_dep hw hₙ,
  end
  -- have hd, from prec.graph.indep_rcns_not_ext_dep hw hc hᵢ,
  -- have hd', from prec.graph.indep_rcns_not_ext_dep hw (ne.symm hc) hᵢ',