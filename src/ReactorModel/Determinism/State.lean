import ReactorModel.Determinism.Dependency

open Classical ReactorType Indexable

namespace Execution
namespace State

variable [Indexable α] {s s₁ s₂ : State α} in section

theorem exec_preserves_tag (rcn : ID) : (s.exec rcn).tag = s.tag :=
  rfl

theorem exec_preserves_progress (s : State α) (rcn : ID) : (s.exec rcn).progress = s.progress :=
  rfl

theorem exec_equiv (s : State α) (rcn : ID) : s.rtr ≈ (s.exec rcn).rtr := by
  simp [exec]
  exact Equivalent.symm $ apply'_equiv _ _

theorem exec_preserves_dependencies (s : State α) (j) : 
    dependencies s.rtr i = dependencies (s.exec j).rtr i := by
  simp [dependencies, Set.ext_iff]
  intro i
  constructor
  all_goals
    intro d
    refine Dependency.equiv ?_ d
    simp [Equivalent.symm, exec_equiv s j]

theorem exec_allows_iff : s.Allows i₂ ↔ (s.exec i₁).Allows i₂ := by
  simp [Allows.def]
  rw [←Equivalent.mem_iff (cpt := .rcn) (exec_equiv s i₁)]
  simp [←exec_preserves_progress s i₁, exec_preserves_dependencies s i₁]

theorem record_triggers_iff : s.Triggers i₂ ↔ (s.record i₁).Triggers i₂ :=
  Triggers.progress_agnostic

theorem record_indep_allows_iff (hi : i₁ ≮[s.rtr]≯ i₂) : s.Allows i₂ ↔ (s.record i₁).Allows i₂ := by
  simp [record, Allows.def]
  intro _
  constructor <;> intro ⟨hd, hp⟩ 
  case mp =>
    constructor
    · exact hd.trans $ Set.subset_insert i₁ s.progress
    · exact Set.mem_insert_iff.not.mpr $ not_or.mpr ⟨hi.not_eq.symm, hp⟩ 
  case mpr =>
    constructor
    · exact fun _ d => Set.mem_insert_iff.mp (hd d) |>.resolve_left (hi.left $ · ▸ d)
    · exact not_or.mp (Set.mem_insert_iff.not.mp hp) |>.right
  
theorem exec_record_indep_allows_iff (hi : i₁ ≮[s.rtr]≯ i₂) : 
    s.Allows i₁ ↔ (s.exec i₂ |>.record i₂).Allows i₁ := 
  exec_allows_iff.trans $ record_indep_allows_iff (hi.equiv $ s.exec_equiv i₂).symm

end

variable [Proper α] {s s₁ s₂ : State α}

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
      exact hi.no_shared_state_deps h₁ h₂ hc
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

theorem indep_output_disjoint_targets (hi : i₁ ≮[s.rtr]≯ i₂) :
    Disjoint (s.output i₁).targets (s.output i₂).targets := by
  cases h₁ : s.rtr[.rcn][i₁] <;> cases h₂ : s.rtr[.rcn][i₂] <;> simp [output, h₁, h₂]
  case some.some rcn₁ rcn₂ => 
    simp [Set.disjoint_iff_forall_ne]
    intro _ _ ⟨_, hc₁, ht₁⟩ _ _ ⟨_, hc₂, ht₂⟩ hc hj
    cases hc; cases hj; cases ht₁; cases ht₂
    replace hc₁ := rcn₁.target_mem_deps hc₁
    replace hc₂ := rcn₂.target_mem_deps hc₂
    cases Dependency.shared_out_dep h₁ h₂ hi.not_eq hc₁ hc₂ <;> simp [hi.left, hi.right] at *
  all_goals simp [List.targets]

theorem exec_indep_comm (hi : rcn₁ ≮[s.rtr]≯ rcn₂) : 
    (s.exec rcn₁).exec rcn₂ = (s.exec rcn₂).exec rcn₁ := by 
  ext1
  case tag => apply exec_preserves_tag
  case progress => apply exec_preserves_progress
  case rtr =>
    conv => lhs; rw [exec, exec_indep_output_eq hi]
    conv => rhs; rw [exec, exec_indep_output_eq hi.symm]
    apply apply'_disjoint_targets_comm $ indep_output_disjoint_targets hi

theorem exec_indep_triggers_iff (hi : i₁ ≮[s.rtr]≯ i₂) : 
    s.Triggers i₂ ↔ (s.exec i₁).Triggers i₂ := by
  constructor <;> intro ⟨ho, ht⟩  
  case mp =>
    have ho' := Equivalent.obj?_rcn_eq (exec_equiv s i₁) ▸ ho
    have ht' := exec_indep_input_eq hi ‹_› ‹_› |>.symm ▸ ht
    exact .intro ho' ht'
  case mpr =>
    have ho' := Equivalent.obj?_rcn_eq (exec_equiv s i₁) |>.symm ▸ ho
    have ht' := exec_indep_input_eq hi ‹_› ‹_› ▸ ht
    exact .intro ho' ht'

theorem exec_record_indep_triggers_iff (hi : i₁ ≮[s.rtr]≯ i₂) : 
    s.Triggers i₁ ↔ (s.exec i₂ |>.record i₂).Triggers i₁ :=
  exec_indep_triggers_iff hi.symm |>.trans record_triggers_iff

namespace State
namespace Execution