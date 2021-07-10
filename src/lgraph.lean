import data.finset 

-- Type `ε` is a `lgraph.edge`-type over ID-type `ι`, if it can produce a `src` and `dst` ID.
class lgraph.edge (ε ι : Type*) :=
  (lsrc : ε → ι)
  (ldst : ε → ι)

-- The proposition that a given set of edges makes connections only between given IDs.
-- This is used to ensure validity of L-graphs.
def finset.are_well_formed_over {ε ι : Type*} [lgraph.edge ε ι] (edges : finset ε) (ids : finset ι) : Prop :=
  ∀ e ∈ edges, (edge.lsrc e) ∈ ids ∧ (edge.ldst e) ∈ ids

variables ι δ ε : Type*
variables [decidable_eq ι] [decidable_eq δ]
variable [lgraph.edge ε ι]

-- A labled multidigraph, i.e. a type of digraphs, where the vertices are IDs, 
-- which are mappable to underlying data and connected by a generic edge type.
@[ext]
structure lgraph :=
  (ids : finset ι)
  (data : ι → δ)
  (edges : finset ε)
  (well_formed : edges.are_well_formed_over ids)

namespace lgraph

  variables {ι δ ε}

  -- Instances to add ∈-notation for IDs, data and edges.
  instance i_mem : has_mem ι (lgraph ι δ ε) := {mem := λ i g, i ∈ g.ids}
  instance d_mem : has_mem δ (lgraph ι δ ε) := {mem := λ d g, ∃ i, g.data i = d}
  instance e_mem : has_mem ε (lgraph ι δ ε) := {mem := λ e g, e ∈ g.edges}

  -- Produces a graph where the data at a given ID `i` is replaced by new data `d`.
  def update_data (g : lgraph ι δ ε) (i : ι) (d : δ) : lgraph ι δ ε :=
    {lgraph . data := function.update g.data i d, ..g} 

  -- Updating data for different IDs is commutative.
  lemma update_data_comm (g : lgraph ι δ ε) {i i' : ι} (d d' : δ) (h : i ≠ i') :
    (g.update_data i d).update_data i' d' = (g.update_data i' d').update_data i d :=
    by simp [update_data, function.update_comm h]

  @[simp]
  lemma update_data_same (g : lgraph ι δ ε) (i : ι) (d : δ) :
    (g.update_data i d).data i = d :=
    by simp [update_data, function.update_same]

  @[simp] 
  lemma update_data_ne (g : lgraph ι δ ε) {i i' : ι} (d : δ) (h : i' ≠ i) :
    (g.update_data i d).data i' = g.data i' :=
    by simp [update_data, function.update_noteq h]

  @[simp]
  lemma update_data_eq_ids (g : lgraph ι δ ε) (i : ι) (d : δ) :
    (g.update_data i d).ids = g.ids :=
    by simp [update_data, refl]

  @[simp]
  lemma update_data_eq_edges (g : lgraph ι δ ε) (i : ι) (d : δ) :
    (g.update_data i d).edges = g.edges :=
    by simp [update_data, refl]

  -- The proposition that an L-graph connects two given vertices with an edge.
  def has_edge_from_to (g : lgraph ι δ ε) (i i' : ι) : Prop :=
    ∃ e ∈ g.edges, (edge.lsrc e, edge.ldst e) = (i, i')

  notation i-g->j := g.has_edge_from_to i j

  -- The proposition that an L-graph connects two given vertices by some path.
  inductive has_path_from_to (g : lgraph ι δ ε) : ι → ι → Prop
    | direct {i i' : ι} : (i-g->i') → has_path_from_to i i'
    | composite {i iₘ i' : ι} : has_path_from_to i iₘ → has_path_from_to iₘ i' → has_path_from_to i i'

  notation i~g~>j := g.has_path_from_to i j

  -- The proposition that a given L-graph is acyclic.
  def is_acyclic (g : lgraph ι δ ε) : Prop := ∀ i, ¬i~g~>i

  -- If two graphs contain the same edges, then any path in one graph must also exist in the other.
  lemma eq_edges_eq_paths {g g' : lgraph ι δ ε} {i i' : ι} (hₚ : g.edges = g'.edges) (hₑ : i~g~>i') :
    i~g'~>i' :=
    begin
      induction hₑ with _ _ p _ _ _ p_α p_ω p_α' p_ω',
        case has_path_from_to.direct {
          rw [has_edge_from_to, hₚ] at p,
          exact has_path_from_to.direct p
        },
        case has_path_from_to.composite {
          exact has_path_from_to.composite p_α' p_ω'
        }
    end

  -- If two graphs contain the same edges and one is acylic, then so is the other.
  lemma eq_edges_acyclic {g g' : lgraph ι δ ε} (hₑ : g.edges = g'.edges) (hₐ : g.is_acyclic) :
    g'.is_acyclic :=
    begin
      unfold is_acyclic,
      intro i,
      by_contradiction h_f,
      have h_c, from eq_edges_eq_paths (symm hₑ) h_f,
      have : ¬(i~g~>i), from hₐ i,
      contradiction
    end

end lgraph 
