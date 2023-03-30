import ReactorModel.Determinism.Dependency

open Classical ReactorType

namespace Execution
namespace State

theorem exec_preserves_tag (s : State) (rcn : ID) : (s.exec rcn).tag = s.tag :=
  rfl

theorem exec_preserves_progress (s : State) (rcn : ID) : (s.exec rcn).progress = s.progress :=
  rfl

theorem exec_equiv (s : State) (rcn : ID) : s.rtr ≈ (s.exec rcn).rtr := by
  simp [exec]
  exact Equivalent.symm $ Reactor.apply'_equiv _ _

theorem target_not_mem_indep_output {s : State} {i} {i₁ i₂ : ID} (h₂ : s.rtr[.rcn][i₂] = some rcn₂) 
    (hi : i₁ ≮[s.rtr]≯ i₂) (hd : ⟨cpt, i⟩ ∈ rcn₂.deps .in) : 
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
    
theorem exec_indep_restriction_eq {s : State} (hi : i₁ ≮[s.rtr]≯ i₂) 
    (h₂ : s.rtr[.rcn][i₂] = some rcn₂) : 
    input.restriction (s.exec i₁) rcn₂ cpt = input.restriction s rcn₂ cpt := by 
  simp [input.restriction]
  apply Partial.ext_restrict 
  intro _ hd
  exact Reactor.apply'_preserves_unchanged $ target_not_mem_indep_output h₂ hi hd  
  
theorem exec_indep_input_eq {s : State} (hi : i₁ ≮[s.rtr]≯ i₂) (h : s.rtr[.rcn][i₂] = some rcn₂)
    (h' : (s.exec i₁).rtr[.rcn][i₂] = some rcn₂) : (s.exec i₁).input i₂ = s.input i₂ := by 
  simp [input, h, h']
  refine ⟨?_, by simp [exec]⟩
  ext1
  injection h' ▸ Equivalent.obj?_rcn_eq (s.exec_equiv i₁) ▸ h with h'
  exact h'.symm ▸ exec_indep_restriction_eq hi h 
    
theorem exec_indep_output_eq {s : State} (hi : i₁ ≮[s.rtr]≯ i₂) : 
    (s.exec i₁).output i₂ = s.output i₂ := by 
  simp [output]
  have e := Equivalent.obj?_rcn_eq $ s.exec_equiv i₁
  cases h : s.rtr[.rcn][i₂] <;> simp [e ▸ h]
  simp [exec_indep_input_eq hi h $ e ▸ h]

theorem indep_output_disjoint {s : State} (hi : rcn₁ ≮[s.rtr]≯ rcn₂) : 
    List.Disjoint (s.output rcn₁) (s.output rcn₂) := by
  cases h₁ : s.rtr[.rcn][rcn₁] <;> cases h₂ : s.rtr[.rcn][rcn₂] <;> simp [output, *]
  case some.some =>
    sorry
    -- generalize ho₁ : s.output rcn₁ = o₁
    -- generalize ho₂ : s.output rcn₂ = o₂
    -- induction o₁ generalizing o₂ <;> cases o₂ <;> simp
    -- case cons.cons hd₁ tl₁ hi hd₂ tl₂ =>
    --   simp [not_or]
    --   split_ands
    --   · sorry 
    --   · sorry 
    --   · sorry 
    --   · sorry 

theorem exec_indep_swap {s : State} (hi : rcn₁ ≮[s.rtr]≯ rcn₂) : 
    (s.exec rcn₁).exec rcn₂ = (s.exec rcn₂).exec rcn₁ := by 
  ext1
  case tag => apply exec_preserves_tag
  case progress => apply exec_preserves_progress
  case rtr =>
    conv => lhs; rw [exec, exec_indep_output_eq hi]
    conv => rhs; rw [exec, exec_indep_output_eq hi.symm]
    exact Reactor.apply'_disjoint_comm $ indep_output_disjoint hi
  
namespace State
namespace Execution