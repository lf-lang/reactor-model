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

-- Note: We could also restate this theorem such that the `m₂` is part of the return value.
theorem exec_objₘ_rcn_eq {s : State} (m₁ : rcn ∈ s.rtr[.rcn]) (m₂ : rcn ∈ (s.exec rcn').rtr[.rcn]) : 
    s.rtr⟦m₁⟧ = (s.exec rcn').rtr⟦m₂⟧ :=
  Equivalent.objₘ_rcn_eq (s.exec_equiv rcn') m₁ |>.choose_spec

theorem target_not_mem_indep_output {s : State} {i} {rcn₁ rcn₂ : ID} {m₂ : rcn₂ ∈ s.rtr[.rcn]}
    (hi : rcn₁ ≮[s.rtr]≯ rcn₂) (hd : ⟨cpt, i⟩ ∈ s.rtr⟦m₂⟧.deps .in) : 
    (s.output rcn₁).All₂ (¬·.Targets cpt i) := by
  apply List.all₂_iff_forall.mpr
  intro c hc
  simp [output] at hc
  split at hc <;> try contradiction
  case inl m₁ =>
    cases cpt
    all_goals
      intro ⟨⟩
      apply absurd hd
    case stv => exact hi.state_mem_rcn₁_deps_not_mem_rcn₂_deps m₂ hc
    all_goals 
      have h := s.rtr⟦m₁⟧.target_mem_deps hc
      exact NotDependent.deps_disjoint hi.left h (by simp [Change.Normal.target]) m₂
    
theorem exec_indep_restriction_eq {s : State} (hi : rcn₁ ≮[s.rtr]≯ rcn₂) (m₁ m₂) : 
    input.restriction (s.exec rcn₁) rcn₂ m₂ cpt = input.restriction s rcn₂ m₁ cpt := by 
  simp [input.restriction]
  rw [←exec_objₘ_rcn_eq m₁ m₂]
  apply Partial.ext_restrict 
  intro _ hd
  exact Reactor.apply'_preserves_unchanged $ target_not_mem_indep_output hi hd  
  
theorem exec_indep_input_eq {s : State} (hi : rcn₁ ≮[s.rtr]≯ rcn₂) (m₁ : rcn₂ ∈ s.rtr[.rcn]) 
    (m₂ : rcn₂ ∈ (s.exec rcn₁).rtr[.rcn]) : (s.exec rcn₁).input rcn₂ = s.input rcn₂ := by 
  simp [input]
  split <;> try contradiction
  refine ⟨?_, by simp [exec]⟩
  ext1
  exact exec_indep_restriction_eq hi m₁ m₂
    
theorem exec_indep_output_eq {s : State} (hi : rcn₁ ≮[s.rtr]≯ rcn₂) : 
    (s.exec rcn₁).output rcn₂ = s.output rcn₂ := by 
  simp [output]
  split <;> split 
  case inl.inl m₂ m₁ => simp [exec_indep_input_eq hi m₁ m₂, exec_objₘ_rcn_eq m₁ m₂]
  case inr.inr => rfl
  case inr.inl h => 
    have := Equivalent.mem_iff (Equivalent.symm $ Reactor.apply'_equiv _ $ s.output rcn₁) |>.mp h
    contradiction
  case inl.inr h _ =>
    have := Equivalent.mem_iff (Reactor.apply'_equiv _ $ s.output rcn₁) |>.mp h
    contradiction

theorem indep_output_disjoint {s : State} (hi : rcn₁ ≮[s.rtr]≯ rcn₂) : 
    List.Disjoint (s.output rcn₁) (s.output rcn₂) := by
  cases h₁ : s.rtr[.rcn][rcn₁] <;> cases h₂ : s.rtr[.rcn][rcn₂]
  case' none.none, none.some =>
    have h₁ : rcn₁ ∉ s.rtr[.rcn] := Partial.mem_iff.not.mpr $ by simp_all
    simp [output, h₁]
  case some.none =>
    have h₂ : rcn₂ ∉ s.rtr[.rcn] := Partial.mem_iff.not.mpr $ by simp_all
    simp [output, h₂]
  case some.some =>
    have h₁ : rcn₁ ∈ s.rtr[.rcn] := Partial.mem_iff.mpr ⟨_, h₁⟩
    have h₂ : rcn₂ ∈ s.rtr[.rcn] := Partial.mem_iff.mpr ⟨_, h₂⟩
    simp [output, h₁, h₂]
    
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