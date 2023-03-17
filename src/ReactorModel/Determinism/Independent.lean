import ReactorModel.Execution

open Classical

structure Independent (rtr : Reactor) (rcn₁ rcn₂ : ID) : Prop where
  source : ¬(rcn₁ [rtr]> rcn₂)
  effect : ¬(rcn₂ [rtr]> rcn₁)

notation rcn₁ " <[" rtr "]> " rcn₂ => Independent rtr rcn₁ rcn₂

namespace Independent

@[symm]
protected theorem symm (h : rcn₁ <[rtr]> rcn₂) : rcn₂ <[rtr]> rcn₁ :=
  ⟨h.effect, h.source⟩ 

-- TODO: Come up with better names for these theorems.

theorem nonoverlapping_deps : 
  (i₁ <[σ]> i₂) → (σ[.rcn][i₁] = some rcn₁) → (σ[.rcn][i₂] = some rcn₂) →
  (rcn₁.deps .out ∩ rcn₂.deps .in) = ∅ := by
  intro ⟨hi, _⟩ ho₁ ho₂
  by_contra hc
  sorry -- exact absurd (ReactorType.Dependency.depOverlap ho₁ ho₂ $ Finset.nonempty_of_ne_empty hc) hi
 
theorem ne_rtr_or_pure : 
  (i₁ <[σ]> i₂) → (i₁ ≠ i₂) →
  (σ[.rcn][i₁] = some rcn₁) → (σ[.rcn][i₂] = some rcn₂) →
  (σ[.rcn][i₁]& = some c₁) → (σ[.rcn][i₂]& = some c₂) →
  (c₁.id ≠ c₂.id) ∨ rcn₁.Pure ∨ rcn₂.Pure := by
  sorry
  /-intro h hn ho₁ ho₂ hc₁ hc₂ 
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
  -/
  
end Independent

-- TODO: This begs the question: Should acyclicity be a requirement of a reactor? Or rather a result
--       of the execution semantics. I.e. if we have s₁ ⇓* s₂, we can conclude that s₁.rtr is acyclic.  
--       (Note: This doesn't quite work as Execution is reflexive).
theorem Execution.State.Allows.requires_acyclic_deps {s : State} : (s.Allows rcn) → (rcn <[s.rtr]> rcn) := by
  sorry
  /-intro ⟨hd, hu⟩
  by_contra h
  simp [Set.subset_def, Reactor.dependencies] at hd
  simp [Independent] at h
  exact absurd (hd _ h) hu
  -/