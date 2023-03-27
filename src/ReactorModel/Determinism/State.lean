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

theorem target_not_mem_indep_output {s : State} {i} {rcn₁ rcn₂ : ID}
    (hi : rcn₁ ≮[s.rtr] rcn₂) (m₂ : rcn₂ ∈ s.rtr[.rcn]) (hd : ⟨cpt, i⟩ ∈ s.rtr⟦m₂⟧.deps .in) : 
    (s.output rcn₁).All₂ (¬·.Targets cpt i) := by
  apply List.all₂_iff_forall.mpr
  intro c hc
  simp [output] at hc
  split at hc <;> try contradiction
  case inl m₁ =>
    intro ⟨⟩ 
    have := hi.deps_disjoint m₁ m₂
    have := s.rtr⟦m₁⟧.targetMemDeps hc
    exact Ne.irrefl $ Set.disjoint_iff_forall_ne.mp ‹_› ‹_› hd

theorem exec_indep_restriction_eq {s : State} (hn : rcn₁ ≠ rcn₂) (hi : rcn₁ ≮[s.rtr] rcn₂) (m₁ m₂) : 
    input.restriction (s.exec rcn₁) rcn₂ m₂ cpt = input.restriction s rcn₂ m₁ cpt := by 
  simp [input.restriction]
  rw [←exec_objₘ_rcn_eq m₁ m₂]
  apply Partial.ext_restrict 
  intro i hd
  exact Reactor.apply'_preserves_unchanged $ target_not_mem_indep_output hi m₁ hd  
  
theorem exec_indep_input_eq {s : State} (hn : rcn₁ ≠ rcn₂) (hi : rcn₁ ≮[s.rtr] rcn₂) : 
    (s.exec rcn₁).input rcn₂ = s.input rcn₂ := by 
  simp [input]
  split <;> split 
  case inr.inr => simp [exec]
  case inr.inl h => 
    have := Equivalent.mem_iff (Equivalent.symm $ Reactor.apply'_equiv _ $ s.output rcn₁) |>.mp h
    contradiction
  case inl.inr h _ =>
    have := Equivalent.mem_iff (Reactor.apply'_equiv _ $ s.output rcn₁) |>.mp h
    contradiction
  case inl.inl m₂ m₁ =>
    refine ⟨?_, by simp [exec]⟩
    ext1
    exact exec_indep_restriction_eq hn hi m₁ m₂
    
namespace State
namespace Execution