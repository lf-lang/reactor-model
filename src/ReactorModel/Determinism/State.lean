import ReactorModel.Determinism.Dependency

open Classical ReactorType Indexable

namespace Execution
namespace State

theorem exec_preserves_tag [Indexable α] (s : State α) (rcn : ID) : (s.exec rcn).tag = s.tag :=
  rfl

theorem exec_preserves_progress [Indexable α] (s : State α) (rcn : ID) : 
    (s.exec rcn).progress = s.progress :=
  rfl

theorem exec_equiv [Indexable α] (s : State α) (rcn : ID) : s.rtr ≈ (s.exec rcn).rtr := by
  simp [exec]
  exact Equivalent.symm $ apply'_equiv _ _

variable [Proper α] {s : State α}

theorem target_not_mem_indep_output 
    (h₂ : s.rtr[.rcn][i₂] = some rcn₂) (hi : i₁ ≮[s.rtr]≯ i₂) (hd : ⟨cpt, i⟩ ∈ rcn₂.deps .in) : 
    (s.output i₁).All₂ (¬·.Targets cpt i) := by
  apply List.all₂_iff_forall.mpr
  intro c hc
  simp [output] at hc
  split at hc <;> try contradiction
  case _ rcn₁ h₁ =>
    cases cpt
    all_goals
      intro ⟨⟩
      apply absurd hd
    case stv => 
      exact hi.state_mem_rcn₁_deps_not_mem_rcn₂_deps h₁ h₂ hc
    all_goals 
      exact hi.left.deps_disjoint h₁ h₂ (rcn₁.target_mem_deps hc) $ by simp [Change.Normal.target]
    
theorem exec_indep_restriction_eq (hi : i₁ ≮[s.rtr]≯ i₂) (h₂ : s.rtr[.rcn][i₂] = some rcn₂) : 
    input.restriction (s.exec i₁) rcn₂ cpt = input.restriction s rcn₂ cpt := by 
  simp [input.restriction]
  apply Partial.ext_restrict 
  intro _ hd
  exact apply'_preserves_unchanged $ target_not_mem_indep_output h₂ hi hd  
  
theorem exec_indep_input_eq 
    (hi : i₁ ≮[s.rtr]≯ i₂) (h : s.rtr[.rcn][i₂] = some rcn₂)
    (h' : (s.exec i₁).rtr[.rcn][i₂] = some rcn₂) : (s.exec i₁).input i₂ = s.input i₂ := by 
  simp [input, h, h']
  refine ⟨?_, by simp [exec]⟩
  ext1
  injection h' ▸ Equivalent.obj?_rcn_eq (s.exec_equiv i₁) ▸ h with h'
  exact h'.symm ▸ exec_indep_restriction_eq hi h 
    
theorem exec_indep_output_eq (hi : i₁ ≮[s.rtr]≯ i₂) : (s.exec i₁).output i₂ = s.output i₂ := by 
  simp [output]
  have e := Equivalent.obj?_rcn_eq $ s.exec_equiv i₁
  cases h : s.rtr[.rcn][i₂] <;> simp [e ▸ h]
  simp [exec_indep_input_eq hi h $ e ▸ h]

theorem indep_normal_output_disjoint (hi : i₁ ≮[s.rtr]≯ i₂) :
    List.Disjoint (s.output i₁ |>.filter (·.IsNormal)) (s.output i₂ |>.filter (·.IsNormal)) := by
  cases h₁ : s.rtr[.rcn][i₁] <;> cases h₂ : s.rtr[.rcn][i₂] <;> simp [output, *]
  case some.some rcn₁ rcn₂ =>
    simp [List.Disjoint, List.mem_filter]
    intro _ hc₁ hn
    cases hn
    case intro c =>
      intro hc₂ _
      replace hc₁ := rcn₁.target_mem_deps hc₁
      replace hc₂ := rcn₂.target_mem_deps hc₂
      simp [Change.Normal.target] at hc₁ hc₂
      cases hc : c.cpt <;> try cases ‹Kind›
      case stv =>
        -- by_cases h : 
        -- have ⟨_, _, h₁, ho₁⟩ := Indexable.obj?_split h₁
        -- have ⟨_, _, h₂, ho₂⟩ := Indexable.obj?_split h₂
        -- 
        -- have := s.rtr.wellformed.overlap_prio h₁ ho₁ (hc ▸ hc₁)
        -- have := s.rtr.wellformed.state_local h₂ ho₂ (hc ▸ hc₂)
        sorry -- You've trying to construct a dependency between 
      case act => sorry
      case prt.in => sorry
      case prt.out => sorry

theorem exec_indep_swap (hi : rcn₁ ≮[s.rtr]≯ rcn₂) : 
    (s.exec rcn₁).exec rcn₂ = (s.exec rcn₂).exec rcn₁ := by 
  ext1
  case tag => apply exec_preserves_tag
  case progress => apply exec_preserves_progress
  case rtr =>
    conv => lhs; rw [exec, exec_indep_output_eq hi]
    conv => rhs; rw [exec, exec_indep_output_eq hi.symm]
    apply apply'_normal_disjoint_comm $ indep_normal_output_disjoint hi
  
namespace State
namespace Execution