import digraph
import network.graph
import network.ids

namespace precedence.graph

  structure edge := 
    (src : reaction.id)
    (dst : reaction.id)

  instance digraph_edge : digraph.edge edge reaction.id := 
    { src := (λ e, e.src), dst := (λ e, e.dst) }

end precedence.graph

def precedence.graph := digraph reaction.id reaction precedence.graph.edge

instance : has_mem reaction precedence.graph := {mem := λ r g, ∃ i, g.data i = r}

namespace precedence.graph

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
    ∀ e : edge, e ∈ ρ.edges ↔ (internally_dependent e.src e.dst ∨ externally_dependent e.src e.dst η)

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

end precedence.graph

-- The proposition, that every well-formed precedence graph over a network is acyclic.
def network.graph.is_prec_acyclic (η : network.graph) : Prop :=
  ∀ ρ : precedence.graph, ρ.is_well_formed_over η → ρ.is_acyclic