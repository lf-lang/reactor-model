import ReactorModel.Inst.PrecGraph.Basic

namespace PrecGraph

variable {ι υ} [ID ι] [Value υ] {σ : Reactor ι υ}

-- A precedence graph contains a path from one reaction to another,
-- if there is a sequence of edges that connects them.
inductive hasPathFromTo (π : PrecGraph σ) : ι → ι → Prop
  | direct {rcn₁ rcn₂} : ⟨rcn₁, rcn₂⟩ ∈ π.edges → hasPathFromTo π rcn₁ rcn₂
  | transitive {rcn₁ rcn₂ rcn₃} : hasPathFromTo π rcn₁ rcn₂ → hasPathFromTo π rcn₂ rcn₃ → hasPathFromTo π rcn₁ rcn₃

notation r:max "~[" π "]~>" s:max => hasPathFromTo π r s

def isAcyclic (π : PrecGraph σ) : Prop := ∀ rcn, ¬(rcn ~[π]~> rcn)

theorem eqEdgesEqPaths {π₁ π₂ : PrecGraph σ} {rcn₁ rcn₂ : ι} (hₑ : π₁.edges = π₂.edges) (hₚ : rcn₁ ~[π₁]~> rcn₂) : 
  rcn₁ ~[π₂]~> rcn₂ := by
  induction hₚ with
  | direct h => 
    simp only [hₑ] at h
    exact hasPathFromTo.direct h
  | transitive _ _ h hₘ => 
    exact hasPathFromTo.transitive h hₘ

theorem eqEdgesAcyclic {π₁ π₂ : PrecGraph σ} (hₑ : π₁.edges = π₂.edges) (hₐ : π₁.isAcyclic) :
  π₂.isAcyclic := by
  simp only [isAcyclic]
  intro k
  byContra hf
  have := eqEdgesEqPaths (Eq.symm hₑ) hf
  have := hₐ k
  contradiction

-- Two reactions are independent in a precedence graph if there are no paths between them.
-- 
-- Note that in order for this property to be non-trivially satisfiable the reactions are
-- constrained to be part of the precedence graph. 
protected structure indep (π : PrecGraph σ) (rcn₁ rcn₂ : ι) : Prop where
  mem₁  : rcn₁ ∈ π.rcns.ids
  mem₂  : rcn₂ ∈ π.rcns.ids
  path₁ : ¬(rcn₁ ~[π]~> rcn₂)
  path₂ : ¬(rcn₂ ~[π]~> rcn₁)

end PrecGraph