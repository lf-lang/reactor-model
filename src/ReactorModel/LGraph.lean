import ReactorModel.Mathlib.Finmap

-- Type `ε` is a `LGraph.Edge`-type over key-type `κ`, if it can produce a `src` and `dst` ID.
class LGraph.Edge (ε κ) :=
  (lsrc : ε → κ)
  (ldst : ε → κ)

variable (κ δ ε : Type _)
variable [DecidableEq κ] [DecidableEq δ] [LGraph.Edge ε κ]

open LGraph

-- A labled multidigraph, i.e. a type of digraphs, where the vertices are IDs, 
-- which are mappable to underlying data and connected by a generic edge type.
structure LGraph :=
  (nodes : κ ⇀ δ)
  (edges : Finset ε)
  (wf : ∀ e ∈ edges, (Edge.lsrc e) ∈ nodes.keys ∧ (Edge.ldst e) ∈ nodes.keys)

namespace LGraph

variable {κ δ ε}

def keys (g : LGraph κ δ ε) : Finset κ := g.nodes.keys

noncomputable def data (g : LGraph κ δ ε) : Finset δ := g.nodes.values
  
-- Instances to add ∈-notation for keys, data and edges.
instance κMem : Mem κ (LGraph κ δ ε) := ⟨(· ∈ ·.keys)⟩
instance δMem : Mem δ (LGraph κ δ ε) := ⟨(· ∈ ·.data)⟩ 
instance εMem : Mem ε (LGraph κ δ ε) := ⟨(· ∈ ·.edges)⟩

-- The proposition that an L-graph connects two given vertices with an edge.
def hasEdgeFromTo (g : LGraph κ δ ε) (k k' : κ) : Prop :=
  ∃ e ∈ g.edges, (Edge.lsrc e = k) ∧ (Edge.ldst e = k')

-- The proposition that an L-graph connects two given vertices by some path.
inductive hasPathFromTo (g : LGraph κ δ ε) : κ → κ → Prop
  | direct {k k' : κ} : (g.hasEdgeFromTo k k') → hasPathFromTo g k k'
  | composite {k kₘ k' : κ} : hasPathFromTo g k kₘ → hasPathFromTo g kₘ k' → hasPathFromTo g k k'

notation k "~" g "~>" l => hasPathFromTo g k l

-- The proposition that a given L-graph is acyclic.
def isAcyclic (g : LGraph κ δ ε) : Prop := ∀ k, ¬(k~g~>k)

-- If two graphs contain the same edges, then any path in one graph must also exist in the other.
theorem eqEdgesEqPaths {g g' : LGraph κ δ ε} {k k' : κ} (hₑ : g.edges = g'.edges) (hₚ : k~g~>k') : 
  k~g'~>k' := by
  induction hₚ with
  | direct h => 
    simp only [hasEdgeFromTo, hₑ] at h
    exact hasPathFromTo.direct h
  | composite _ _ h hₘ => 
    exact hasPathFromTo.composite h hₘ

-- If two graphs contain the same edges and one is acylic, then so is the other.
theorem eqEdgesAcyclic {g g' : LGraph κ δ ε} (hₑ : g.edges = g'.edges) (hₐ : g.isAcyclic) :
  g'.isAcyclic := by
  simp only [isAcyclic]
  intro k
  byContra hf
  have := eqEdgesEqPaths (Eq.symm hₑ) hf
  have := hₐ k
  contradiction

end LGraph 