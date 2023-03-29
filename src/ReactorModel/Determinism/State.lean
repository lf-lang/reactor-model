import ReactorModel.Determinism.Dependency

open Classical ReactorType

namespace Execution
namespace State

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
      have h := s.rtr⟦m₁⟧.targetMemDeps hc
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

namespace State
namespace Execution