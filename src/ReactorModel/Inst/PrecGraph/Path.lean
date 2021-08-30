import ReactorModel.Inst.PrecGraph.Basic

namespace PrecGraph

variable {ι υ} [ID ι] [Value υ] {η : Network ι υ}

def hasEdgeFromTo (π : PrecGraph η) (rcn₁ rcn₂ : ι) : Prop :=
  ∃ e ∈ π.edges, e.src = rcn₁ ∧ e.dst = rcn₂

inductive hasPathFromTo (π : PrecGraph η) : ι → ι → Prop
  | direct {rcn₁ rcn₂} : (π.hasEdgeFromTo rcn₁ rcn₂) → hasPathFromTo π rcn₁ rcn₂
  | transitive {rcn₁ rcn₂ rcn₃} : hasPathFromTo π rcn₁ rcn₂ → hasPathFromTo π rcn₂ rcn₃ → hasPathFromTo π rcn₁ rcn₃

notation r "~" π "~>" s => hasPathFromTo π r s

def isAcyclic (π : PrecGraph η) : Prop := ∀ rcn, ¬(rcn ~π~> rcn)

theorem eqEdgesEqPaths {π₁ π₂ : PrecGraph η} {rcn₁ rcn₂ : ι} (hₑ : π₁.edges = π₂.edges) (hₚ : rcn₁ ~π₁~> rcn₂) : 
  rcn₁ ~π₂~> rcn₂ := by
  induction hₚ with
  | direct h => 
    simp only [hasEdgeFromTo, hₑ] at h
    exact hasPathFromTo.direct h
  | transitive _ _ h hₘ => 
    exact hasPathFromTo.transitive h hₘ

theorem eqEdgesAcyclic {π₁ π₂ : PrecGraph η} (hₑ : π₁.edges = π₂.edges) (hₐ : π₁.isAcyclic) :
  π₂.isAcyclic := by
  simp only [isAcyclic]
  intro k
  byContra hf
  have := eqEdgesEqPaths (Eq.symm hₑ) hf
  have := hₐ k
  contradiction

-- Two reactions are independent in a precedence graph if there are no paths between them.
-- This property trivially holds for all reactions that are not part of the precedence graph.
-- Hence most uses of this property should also constrain `i` and `i'` to be `∈ ρ.ids`.
def indep (π : PrecGraph η) (rcn₁ rcn₂ : ι) : Prop := ¬(rcn₁ ~π~> rcn₂) ∧ ¬(rcn₂ ~π~> rcn₁)

end PrecGraph

-- The proposition, that every well-formed precedence graph over a network is acyclic.
def Network.isPrecAcyclic {ι υ} [ID ι] [Value υ] (η : Network ι υ) : Prop :=
  ∀ π : PrecGraph η, π.isAcyclic