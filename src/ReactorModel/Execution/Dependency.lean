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
  (rcn₁.deps .out ∩ rcn₂.deps .in) = ∅ := by
  intro ⟨hi, _⟩ ho₁ ho₂
  by_contra hc
  simp [Finset.eq_empty_iff_forall_not_mem] at hc
  exact absurd (Dependency.depOverlap ho₁ ho₂ hc) hi

theorem ne_rtr_or_pure : 
  (i₁ ≠ i₂) → -- keep this?
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (σ.con? .rcn i₁ = some c₁) → (σ.con? .rcn i₂ = some c₂) →
  (c₁.id ≠ c₂.id) ∨ rcn₁.isPure ∨ rcn₂.isPure := by
  intro hn h ho₁ ho₂ hc₁ hc₂ 
  by_contra hc
  have ⟨hc, hp⟩ := (not_or ..).mp hc
  simp [not_or] at hp hc
  have he := Reactor.con?_eq_id_to_eq hc₁ hc₂ hc
  simp [he] at hc₁
  have ⟨_, ho₁', hcm₁⟩ := Reactor.con?_to_obj?_and_cmp? hc₁
  have ⟨_, ho₂', hcm₂⟩ := Reactor.con?_to_obj?_and_cmp? hc₂
  have ho₁'' := ho₁'.symm.trans ho₁
  have ho₂'' := ho₂'.symm.trans ho₂
  simp [ho₁'', ho₂''] at hcm₁ hcm₂
  have hre := hc₂.trans hc₁.symm
  by_cases hm₁ : rcn₁.isMut 
  case pos =>
    by_cases hm₂ : rcn₂.isMut
    case pos =>
      cases c₂.obj.orderability (.muts hcm₁ hcm₂ hn hm₁ hm₂)
      case inl hpr =>
        have hd := Dependency.prio hre ho₂ ho₁ (by simp [hm₁, hm₂]) hpr
        exact absurd hd h.right 
      case inr hpr =>
        have hd := Dependency.prio hre.symm ho₁ ho₂ (by simp [hm₁, hm₂]) hpr
        exact absurd hd h.left 
    case neg => 
      have hd := Dependency.mutNorm hre.symm ho₁ ho₂ hm₁ (by simp_all [Reaction.isMut])
      exact absurd hd h.left 
  case neg =>
    by_cases hm₂ : rcn₂.isMut
    case pos =>
      have hd := Dependency.mutNorm hre ho₂ ho₁ hm₂ (by simp_all [Reaction.isMut])
      exact absurd hd h.right 
    case neg =>
      cases c₂.obj.orderability (.impure hcm₁ hcm₂ hn hp.left hp.right)
      case inl hpr =>
        have hd := Dependency.prio hre ho₂ ho₁ (by simp [hm₁, hm₂]) hpr
        exact absurd hd h.right 
      case inr hpr =>
        have hd := Dependency.prio hre.symm ho₁ ho₂ (by simp [hm₁, hm₂]) hpr
        exact absurd hd h.left 
  

end Indep