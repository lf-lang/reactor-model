import ReactorModel.Mathlib.Finmap

-- Type `ε` is a `LGraph.Edge`-type over ID-type `ι`, if it can produce a `src` and `dst` ID.
class LGraph.Edge (ε ι) :=
  (lsrc : ε → ι)
  (ldst : ε → ι)

variable (ι δ ε : Type _)
variable [DecidableEq ι] [DecidableEq δ] [LGraph.Edge ε ι]

open LGraph

-- A labled multidigraph, i.e. a type of digraphs, where the vertices are IDs, 
-- which are mappable to underlying data and connected by a generic edge type.
structure LGraph :=
  (nodes : ι ⇀ δ)
  (edges : Finset ε)
  (wf : ∀ e ∈ edges, (Edge.lsrc e) ∈ nodes.ids ∧ (Edge.ldst e) ∈ nodes.ids)

namespace LGraph

variable {ι δ ε}

noncomputable def ids (g : LGraph ι δ ε) : Finset ι := g.nodes.ids

noncomputable def data (g : LGraph ι δ ε) : Finset δ := g.nodes.data
  
-- Instances to add ∈-notation for keys, data and edges.
instance ιMem : Mem ι (LGraph ι δ ε) := ⟨(· ∈ ·.ids)⟩
instance δMem : Mem δ (LGraph ι δ ε) := ⟨(· ∈ ·.data)⟩ 
instance εMem : Mem ε (LGraph ι δ ε) := ⟨(· ∈ ·.edges)⟩

-- The proposition that an L-graph connects two given vertices with an edge.
def hasEdgeFromTo (g : LGraph ι δ ε) (k k' : ι) : Prop :=
  ∃ e ∈ g.edges, (Edge.lsrc e = k) ∧ (Edge.ldst e = k')

-- The proposition that an L-graph connects two given vertices by some path.
inductive hasPathFromTo (g : LGraph ι δ ε) : ι → ι → Prop
  | direct {k k' : ι} : (g.hasEdgeFromTo k k') → hasPathFromTo g k k'
  | composite {k kₘ k' : ι} : hasPathFromTo g k kₘ → hasPathFromTo g kₘ k' → hasPathFromTo g k k'

notation k "~" g "~>" l => hasPathFromTo g k l

-- The proposition that a given L-graph is acyclic.
def isAcyclic (g : LGraph ι δ ε) : Prop := ∀ k, ¬(k~g~>k)

-- If two graphs contain the same edges, then any path in one graph must also exist in the other.
theorem eqEdgesEqPaths {g g' : LGraph ι δ ε} {k k' : ι} (hₑ : g.edges = g'.edges) (hₚ : k~g~>k') : 
  k~g'~>k' := by
  induction hₚ with
  | direct h => 
    simp only [hasEdgeFromTo, hₑ] at h
    exact hasPathFromTo.direct h
  | composite _ _ h hₘ => 
    exact hasPathFromTo.composite h hₘ

-- If two graphs contain the same edges and one is acylic, then so is the other.
theorem eqEdgesAcyclic {g g' : LGraph ι δ ε} (hₑ : g.edges = g'.edges) (hₐ : g.isAcyclic) :
  g'.isAcyclic := by
  simp only [isAcyclic]
  intro k
  byContra hf
  have := eqEdgesEqPaths (Eq.symm hₑ) hf
  have := hₐ k
  contradiction

end LGraph 