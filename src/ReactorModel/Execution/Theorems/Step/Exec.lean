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

theorem applied_rtr_eq (e : s₁ ↓ₑ s₂) : e.applied.rtr = s₂.rtr := by
  cases e
  simp [applied, record_preserves_rtr]

theorem preserves_tag (e : s₁ ↓ₑ s₂) : s₁.tag = s₂.tag := by
  simp [e.dst_eq, State.record_preserves_tag, e.apply.preserves_tag]

theorem equiv (e : s₁ ↓ₑ s₂) : s₁.rtr ≈ s₂.rtr := by
  simp [e.dst_eq, State.record_preserves_rtr, e.apply.equiv]

theorem progress_eq (e : s₁ ↓ₑ s₂) : s₂.progress = s₁.progress.insert e.rcn := by 
  simp [e.dst_eq, State.record_progress_eq, e.apply.preserves_progress]

theorem preserves_nontrivial {e : s₁ ↓ₑ s₂} (n : s₁.Nontrivial) : s₂.Nontrivial :=
  n.equiv e.equiv

theorem preserves_independent (e : s₁ ↓ₑ s₂) (h : rcn₁ ≮[s₁.rtr]≯ rcn₂) : rcn₁ ≮[s₂.rtr]≯ rcn₂ :=
  h.equiv e.equiv

theorem preserves_dependencies (e : s₁ ↓ₑ s₂) : 
    dependencies s₁.rtr i = dependencies s₂.rtr i := by
  simp [dependencies, Set.ext_iff]
  intro i
  constructor <;> (intro d; refine Dependency.equiv ?_ d)
  case mp  => exact Equivalent.symm e.equiv
  case mpr => exact e.equiv


theorem indep_allows_iff (e : s₁ ↓ₑ s₂) (hi : i ≮[s₁.rtr]≯ e.rcn) : 
    s₁.Allows i ↔ s₂.Allows i := by
  simp [Allows.def]
  rw [←Equivalent.mem_iff (cpt := .rcn) e.equiv, e.progress_eq]
  sorry -- exec_preserves_dependencies s i₁
  -- exec_allows_iff.trans $ Allows.iff_record_indep (hi.equiv $ s.exec_equiv i₂).symm


end Execution.Step.Exec

namespace Execution.Step.Exec

variable [Proper α] {s s₁ : State α} {rcn : Reaction}

theorem indep_restriction_eq  
    (e : s₁ ↓ₑ s₂) (hi : e.rcn ≮[s₁.rtr]≯ i) (ho : s₁.rtr[.rcn][i] = some rcn) : 
    input.restriction s₁ rcn cpt = input.restriction s₂ rcn cpt := by 
  simp [input.restriction]
  apply Partial.ext_restrict 
  intro _ hd
  exact e.applied_rtr_eq ▸ e.apply.preserves_unchanged $ State.target_not_mem_indep_output ho hi hd  

theorem indep_input_eq 
    (e : s₁ ↓ₑ s₂) (hi : e.rcn ≮[s₁.rtr]≯ i) (h₁ : s₁.rtr[.rcn][i] = some rcn)
    (h₂ : s₂.rtr[.rcn][i] = some rcn) : s₁.input i = s₂.input i := by 
  simp [input, h₁, h₂]
  refine ⟨?_, e.preserves_tag⟩
  ext1
  exact e.indep_restriction_eq hi h₁

theorem indep_output_eq (e : s₁ ↓ₑ s₂) (hi : e.rcn ≮[s₁.rtr]≯ i) : s₁.output i = s₂.output i := by 
  simp [output]
  have he := Equivalent.obj?_rcn_eq e.equiv
  cases h : s₁.rtr[.rcn][i] <;> simp [he ▸ h]
  simp [e.indep_input_eq hi h $ he ▸ h]

theorem indep_comm 
    (e₁ : s ↓ₑ s₁) (e₁₂ : s₁ ↓ₑ s₁₂) (e₂ : s ↓ₑ s₂) (e₂₁ : s₂ ↓ₑ s₂₁) 
    (hr₁ : e₁.rcn = e₂₁.rcn) (hr₂ : e₂.rcn = e₁₂.rcn) (hi : e₁.rcn ≮[s.rtr]≯ e₂.rcn) : 
    s₁₂ = s₂₁ := by 
  have ho₁ := e₁.indep_output_eq hi
  have ho₂ := e₂.indep_output_eq hi.symm
  cases e₁; cases e₁₂; cases e₂; cases e₂₁
  case _ rcn₁ s₁ _ _ a₁ rcn₂ s₁₂ _ _ a₁₂ _ s₂ _ _ a₂ _ s₂₁ _ _ a₂₁ => 
    cases hr₁; cases hr₂; simp [Exec.rcn] at *
    have ⟨z₁₂, f₁₂⟩ := Apply.RTC.construct s₁ (s.output rcn₂)
    have ⟨z₂₁, f₂₁⟩ := Apply.RTC.construct s₂ (s.output rcn₁)
    rw [←ho₁] at a₁₂; rw [←ho₂] at a₂₁
    cases f₁₂.comm_record a₁₂; cases f₂₁.comm_record a₂₁
    rw [record_comm]; congr
    exact Apply.RTC.disjoint_targets_comm (s.indep_output_disjoint_targets hi) a₁ f₁₂ a₂ f₂₁

theorem indep_triggers_iff (e : s₁ ↓ₑ s₂) (hi : i ≮[s₁.rtr]≯ e.rcn) : 
    s₁.Triggers i ↔ s₂.Triggers i := by
  constructor <;> intro ⟨ho, ht⟩  
  case mp =>
    have ho' := Equivalent.obj?_rcn_eq e.equiv ▸ ho
    have ht' := e.indep_input_eq hi.symm ‹_› ‹_› ▸ ht
    exact ⟨ho', ht'⟩ 
  case mpr =>
    have ho' := Equivalent.obj?_rcn_eq e.equiv |>.symm ▸ ho
    have ht' := e.indep_input_eq hi.symm ‹_› ‹_› |>.symm ▸ ht
    exact ⟨ho', ht'⟩ 

end Execution.Step.Exec
