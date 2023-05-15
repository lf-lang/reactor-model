import ReactorModel.Execution.Theorems.Step.Apply

open Classical ReactorType Execution State

namespace Execution.Step.Exec

variable [Indexable α] {s₁ : State α}

def rcn :                  (s₁ ↓ₑ s₂) → ID                               | mk (rcn := r) .. => r
def applied :              (s₁ ↓ₑ s₂) → State α                          | mk (s₂ := s) .. => s
theorem allows_rcn :   (e : s₁ ↓ₑ s₂) → Allows s₁ e.rcn                  | mk a .. => a
theorem triggers_rcn : (e : s₁ ↓ₑ s₂) → Triggers s₁ e.rcn                | mk _ t _ => t
theorem apply :        (e : s₁ ↓ₑ s₂) → s₁ -[s₁.output e.rcn]→ e.applied | mk _ _ a => a
theorem dst_eq :       (e : s₁ ↓ₑ s₂) → s₂ = e.applied.record e.rcn      | mk .. => rfl

theorem preserves_tag (e : s₁ ↓ₑ s₂) : s₁.tag = s₂.tag := by
  simp [e.dst_eq, State.record_preserves_tag, e.apply.preserves_tag]

theorem equiv (e : s₁ ↓ₑ s₂) : s₁.rtr ≈ s₂.rtr := by
  simp [e.dst_eq, State.record_preserves_rtr, e.apply.equiv]

theorem progress_eq (e : s₁ ↓ₑ s₂) : s₂.progress = s₁.progress.insert e.rcn := by 
  simp [e.dst_eq, State.record_progress_eq, e.apply.preserves_progress]

theorem preserves_nontrivial {e : s₁ ↓ₑ s₂} (n : s₁.Nontrivial) : s₂.Nontrivial :=
  n.equiv e.equiv

end Execution.Step.Exec

/-
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
-/

/-
theorem record_exec_comm {s : State α} {rcn₁ rcn₂ : ID} : 
    (s.record rcn₁).exec rcn₂ = (s.exec rcn₂).record rcn₁ := by
  simp [exec]
  rw [←output_congr (s₁ := s) (s₂ := record s rcn₁) (i := rcn₂)]
  exact record_apply'_comm

theorem exec_indep_comm (hi : rcn₁ ≮[s.rtr]≯ rcn₂) : 
    (s.exec rcn₁).exec rcn₂ = (s.exec rcn₂).exec rcn₁ := by 
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
  exec_indep_triggers_iff hi.symm |>.trans Triggers.iff_record
-/

/-
theorem exec_record_indep_allows_iff (hi : i₁ ≮[s.rtr]≯ i₂) : 
    s.Allows i₁ ↔ (s.exec i₂ |>.record i₂).Allows i₁ := 
  exec_allows_iff.trans $ Allows.iff_record_indep (hi.equiv $ s.exec_equiv i₂).symm
-/

/-
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
  refine ⟨?_, exec_preserves_tag _⟩
  ext1
  injection h' ▸ Equivalent.obj?_rcn_eq (s.exec_equiv i₁) ▸ h with h'
  exact h'.symm ▸ exec_indep_restriction_eq hi h 

theorem exec_indep_output_eq (hi : i₁ ≮[s.rtr]≯ i₂) : (s.exec i₁).output i₂ = s.output i₂ := by 
  simp [output]
  have e := Equivalent.obj?_rcn_eq $ s.exec_equiv i₁
  cases h : s.rtr[.rcn][i₂] <;> simp [e ▸ h]
  simp [exec_indep_input_eq hi h $ e ▸ h]
-/