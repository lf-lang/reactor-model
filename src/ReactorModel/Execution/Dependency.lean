import ReactorModel.Components

open Classical

-- About the norm-condition in prio: 
-- We want to establish a dependency between mutations with priorities 
-- as well normal reactions with priorities, but not between normal reactions
-- and mutations. Otherwise a normal reaction might take precedence over
-- a mutation. Also the precedence of mutations over normal reactions is
-- handled by mutNorm - so this would potentially just create a redundancy.
inductive Dependency (σ : Reactor) : ID → ID → Prop
  | prio :
    (σ.con? .rcn i₁ = σ.con? .rcn i₂) →
    (σ.obj? .rcn i₁ = some rcn₁) →
    (σ.obj? .rcn i₂ = some rcn₂) →
    (rcn₁.isMut ↔ rcn₂.isMut) → 
    (rcn₁.prio > rcn₂.prio) →
    Dependency σ i₁ i₂
  | mutNorm :
    (σ.con? .rcn iₘ = σ.con? .rcn iₙ) →
    (σ.obj? .rcn iₘ = some m) →
    (σ.obj? .rcn iₙ = some n) →
    (m.isMut) → 
    (n.isNorm) → 
    Dependency σ iₘ iₙ
  | depOverlap :
    (σ.obj? .rcn (i₁ : ID) = some rcn₁) →
    (σ.obj? .rcn (i₂ : ID) = some rcn₂) →
    ((rcn₁.deps .out ∩ rcn₂.deps .in).nonempty) →
    Dependency σ i₁ i₂
  | mutNest :
    (σ.obj? .rcn (iₘ : ID) = some m) → 
    (m.isMut) → 
    (σ.con? .rcn iₘ = some rtr₁) →
    (rtr₂ ∈ rtr₁.obj.nest.values) → 
    (iᵣ ∈ rtr₂.rcns.ids) → 
    Dependency σ iₘ iᵣ
  | trans : 
    Dependency σ i₁ i₂ → 
    Dependency σ i₂ i₃ → 
    Dependency σ i₁ i₃

notation i₁:max " >[" σ "] " i₂:max => Dependency σ i₁ i₂

def Reactor.dependencies (σ : Reactor) (rcn : ID) : Set ID := { rcn' | rcn' >[σ] rcn }

def Indep (σ : Reactor) (rcn₁ rcn₂ : ID) : Prop :=
  ¬(rcn₁ >[σ] rcn₂) ∧ ¬(rcn₂ >[σ] rcn₁)

notation i₁:max " >[" σ "]< " i₂:max => Indep σ i₁ i₂

namespace Indep

protected theorem symm : (rcn₁ >[σ]< rcn₂) → (rcn₂ >[σ]< rcn₁) :=
  And.symm

-- TODO: Come up with better names for these theorems.

theorem nonoverlapping_deps : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (rcn₁.deps .out ∩ rcn₂.deps .«in») = ∅ := by
  intro ⟨hi, _⟩ ho₁ ho₂
  by_contra hc
  simp [Finset.eq_empty_iff_forall_not_mem] at hc
  exact absurd (Dependency.depOverlap ho₁ ho₂ hc) hi

theorem ne_rtr_or_pure : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (σ.con? .rcn i₁ = some c₁) → (σ.con? .rcn i₂ = some c₂) →
  (c₁.id ≠ c₂.id) ∨ rcn₁.isPure ∨ rcn₂.isPure := by
  intro h ho₁ ho₂ hc₁ hc₂ 
  by_contra hc
  have ⟨hc, hp⟩ := (not_or ..).mp hc
  simp [not_or] at hp hc
  -- have ⟨rtr₁, hc₁, hr₁⟩ := Reactor.obj?_to_con?_and_cmp? ho₁
  -- have ⟨rtr₂, hc₂, hr₂⟩ := Reactor.obj?_to_con?_and_cmp? ho₂
  -- rw [hc] at hc₁
  -- simp [Option.some_inj.mp $ hc₁.symm.trans hc₂, Reactor.cmp?] at hr₁ hr₂
  sorry
  /-cases rtr₂.obj.rcnsTotalOrder (.impure hr₁ hr₂ sorry hp.left hp.right)
  case h.inl hp => exact absurd (.internal $ .prio hc.symm h₂ h₁ hp) h.right
  case h.inr hp => exact absurd (.internal $ .rcns hc      h₁ h₂ hp) h.left  
  -/

end Indep