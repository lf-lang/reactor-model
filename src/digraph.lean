import data.finset 

-- Type `ε` is a `digraph.edge`-type over ID-type `ι`, if it can produce a `src` and `dst` ID.
class digraph.edge (ε ι : Type*) :=
  (src : ε → ι)
  (dst : ε → ι)

-- The proposition that a given set of edges makes connections only between given IDs.
-- This is used to ensure validity of digraphs.
def digraph.edges_are_formed_over_ids {ε ι : Type*} [digraph.edge ε ι] (edges : finset ε) (ids : finset ι) : Prop :=
  ∀ e ∈ edges, (edge.src e) ∈ ids ∧ (edge.dst e) ∈ ids

variables ι δ ε : Type*
variables [decidable_eq ι] [decidable_eq δ]
variable [digraph.edge ε ι]

-- A type of digraphs, where the vertices are IDs, which are mappable to underlying data and connected by a generic edge type.
@[ext]
structure digraph :=
  (ids : finset ι)
  (data : ι → δ)
  (edges : finset ε)
  (validity : digraph.edges_are_formed_over_ids edges ids)

namespace digraph

  variables {ι δ ε}

  -- Instances to add ∈-notation for IDs, data and edges.
  instance i_mem : has_mem ι (digraph ι δ ε) := {mem := λ i g, i ∈ g.ids}
  instance d_mem : has_mem δ (digraph ι δ ε) := {mem := λ d g, ∃ i, g.data i = d}
  instance e_mem : has_mem ε (digraph ι δ ε) := {mem := λ e g, e ∈ g.edges}

  -- Produces a graph where the data at a given ID `i` is replaced by new data `d`.
  def update_data (g : digraph ι δ ε) (i : ι) (d : δ) : digraph ι δ ε :=
    {digraph . data := function.update g.data i d, ..g} 

  -- Updating data for different IDs is commutative.
  lemma update_data_comm (g : digraph ι δ ε) {i i' : ι} (d d' : δ) (h : i ≠ i') :
    (g.update_data i d).update_data i' d' = (g.update_data i' d').update_data i d :=
    by simp [update_data, function.update_comm h]

  @[simp]
  lemma update_data_same (g : digraph ι δ ε) (i : ι) (d : δ) :
    (g.update_data i d).data i = d :=
    by simp [update_data, function.update_same]

  @[simp] 
  lemma update_data_ne (g : digraph ι δ ε) {i i' : ι} (d : δ) (h : i' ≠ i) :
    (g.update_data i d).data i' = g.data i' :=
    by simp [update_data, function.update_noteq h]

  @[simp]
  lemma update_data_eq_ids (g : digraph ι δ ε) (i : ι) (d : δ) :
    (g.update_data i d).ids = g.ids :=
    by simp [update_data, refl]

  @[simp]
  lemma update_data_eq_edges (g : digraph ι δ ε) (i : ι) (d : δ) :
    (g.update_data i d).edges = g.edges :=
    by simp [update_data, refl]

  -- The proposition that a digraph connects two given vertices with an edge.
  def has_edge_from_to (g : digraph ι δ ε) (i i' : ι) : Prop :=
    ∃ e ∈ g.edges, (edge.src e, edge.dst e) = (i, i')

  notation i-g->j := g.has_edge_from_to i j

  -- The proposition that a digraph connects two given vertices by some path.
  inductive has_path_from_to (g : digraph ι δ ε) : ι → ι → Prop
    | direct {i i' : ι} : (i-g->i') → has_path_from_to i i'
    | composite {i iₘ i' : ι} : has_path_from_to i iₘ → has_path_from_to iₘ i' → has_path_from_to i i'

  notation i~g~>j := g.has_path_from_to i j

  -- The proposition that a given digraph is acyclic.
  def is_acyclic (g : digraph ι δ ε) : Prop := ∀ i, ¬i~g~>i

  -- If two graphs contain the same edges, then any path in one graph must also exist in the other.
  lemma eq_edges_eq_paths {g g' : digraph ι δ ε} {i i' : ι} (hₚ : g.edges = g'.edges) (hₑ : i~g~>i') :
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
  lemma eq_edges_acyclic {g g' : digraph ι δ ε} (hₑ : g.edges = g'.edges) (hₐ : g.is_acyclic) :
    g'.is_acyclic :=
    begin
      unfold is_acyclic,
      intro i,
      by_contradiction h_f,
      have h_c, from eq_edges_eq_paths (symm hₑ) h_f,
      have : ¬(i~g~>i), from hₐ i,
      contradiction
    end

end digraph 
