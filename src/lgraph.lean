import data.finset
import data.finmap  
import mathlib

-- Type `ε` is a `lgraph.edge`-type over key-type `κ`, if it can produce a `src` and `dst` ID.
class lgraph.edge (ε κ : Type*) :=
  (lsrc : ε → κ)
  (ldst : ε → κ)

variables κ δ ε : Type*
variables [decidable_eq κ] [decidable_eq δ] [lgraph.edge ε κ]

-- A labled multidigraph, i.e. a type of digraphs, where the vertices are IDs, 
-- which are mappable to underlying data and connected by a generic edge type.
@[ext]
structure lgraph :=
  (nodes : κ ⇀ δ)
  (edges : finset ε)
  (well_formed : ∀ e ∈ edges, (edge.lsrc e) ∈ nodes.keys ∧ (edge.ldst e) ∈ nodes.keys)

namespace lgraph

  variables {κ δ ε}

  def keys (g : lgraph κ δ ε) : finset κ := g.nodes.keys

  noncomputable def data (g : lgraph κ δ ε) : finset δ := g.nodes.values
    
  -- Instances to add ∈-notation for keys, data and edges.
  instance κ_mem : has_mem κ (lgraph κ δ ε) := ⟨λ i g, i ∈ g.keys⟩
  instance δ_mem : has_mem δ (lgraph κ δ ε) := ⟨λ d g, d ∈ g.data⟩ 
  instance ε_mem : has_mem ε (lgraph κ δ ε) := ⟨λ e g, e ∈ g.edges⟩

  -- The proposition that an L-graph connects two given vertices with an edge.
  def has_edge_from_to (g : lgraph κ δ ε) (k k' : κ) : Prop :=
    ∃ e ∈ g.edges, (edge.lsrc e = k) ∧ (edge.ldst e = k')

  notation k-g->l := g.has_edge_from_to k l

  -- The proposition that an L-graph connects two given vertices by some path.
  inductive has_path_from_to (g : lgraph κ δ ε) : κ → κ → Prop
    | direct {k k' : κ} : (k-g->k') → has_path_from_to k k'
    | composite {k kₘ k' : κ} : has_path_from_to k kₘ → has_path_from_to kₘ k' → has_path_from_to k k'

  notation k~g~>l := g.has_path_from_to k l

  -- The proposition that a given L-graph is acyclic.
  def is_acyclic (g : lgraph κ δ ε) : Prop := ∀ k, ¬(k~g~>k)

  -- If two graphs contain the same edges, then any path in one graph must also exist in the other.
  lemma eq_edges_eq_paths {g g' : lgraph κ δ ε} {k k' : κ} (hₑ : g.edges = g'.edges) (hₚ : k~g~>k') :
    k~g'~>k' :=
    begin
      induction hₚ with _ _ p _ _ _ p_α p_ω p_α' p_ω',
        case has_path_from_to.direct {
          rw [has_edge_from_to, hₑ] at p,
          exact has_path_from_to.direct p
        },
        case has_path_from_to.composite {
          exact has_path_from_to.composite p_α' p_ω'
        }
    end

  -- If two graphs contain the same edges and one is acylic, then so is the other.
  lemma eq_edges_acyclic {g g' : lgraph κ δ ε} (hₑ : g.edges = g'.edges) (hₐ : g.is_acyclic) :
    g'.is_acyclic :=
    begin
      unfold is_acyclic,
      intro k,
      by_contradiction h_f,
      have h_c, from eq_edges_eq_paths (symm hₑ) h_f,
      have : ¬(k~g~>k), from hₐ k,
      contradiction
    end

end lgraph 