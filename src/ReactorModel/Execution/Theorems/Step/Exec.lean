import ReactorModel.Execution.Theorems.Step.Apply

open Classical Reactor Execution State

namespace Execution.Step.Exec

variable [Hierarchical α] {s₁ : State α}

def rcn :                  (s₁ ↓ᵉ s₂) → ID                                       | mk (rcn := r) .. => r
def clock :                (s₁ ↓ᵉ s₂) → _root_.Time                              | mk (t := t) .. => t
def applied :              (s₁ ↓ᵉ s₂) → State α                                  | mk (s₂ := s) .. => s
theorem allows_rcn :   (e : s₁ ↓ᵉ s₂) → Allows s₁ e.rcn                          | mk a .. => a
theorem triggers_rcn : (e : s₁ ↓ᵉ s₂) → Triggers s₁ e.rcn                        | mk _ t .. => t
theorem apply :        (e : s₁ ↓ᵉ s₂) → s₁ -[s₁.output e.rcn]→ e.applied         | mk _ _ a _ => a
theorem clock_le :     (e : s₁ ↓ᵉ s₂) → s₁.clock ≤ e.clock                       | mk _ _ _ c => c
theorem dst_eq :       (e : s₁ ↓ᵉ s₂) → s₂ = (e.applied.at e.clock).record e.rcn | mk .. => rfl

theorem applied_rtr_eq (e : s₁ ↓ᵉ s₂) : e.applied.rtr = s₂.rtr := by
  cases e
  simp [applied, record_preserves_rtr, at_preserves_rtr]

theorem preserves_tag (e : s₁ ↓ᵉ s₂) : s₁.tag = s₂.tag := by
  simp [e.dst_eq, record_preserves_tag, e.apply.preserves_tag, at_preserves_tag]

theorem equiv (e : s₁ ↓ᵉ s₂) : s₁.rtr ≈ s₂.rtr := by
  simp [e.dst_eq, record_preserves_rtr, at_preserves_rtr, e.apply.equiv]

theorem progress_eq (e : s₁ ↓ᵉ s₂) : s₂.progress = s₁.progress.insert e.rcn := by 
  simp [e.dst_eq, record_progress_eq, at_preserves_progress, e.apply.preserves_progress]

theorem preserves_nontrivial {e : s₁ ↓ᵉ s₂} (n : s₁.Nontrivial) : s₂.Nontrivial :=
  n.equiv e.equiv

theorem indep_allows_iff (e : s₁ ↓ᵉ s₂) (hi : i ≮[s₁.rtr]≯ e.rcn) : 
    s₁.Allows i ↔ s₂.Allows i := by
  have a := e.apply
  replace hi := (at_preserves_rtr e.applied e.clock).symm ▸ a.preserves_independent hi
  simp [
    e.dst_eq, ←Allows.iff_record_indep hi.symm, ←Allows.iff_at (s := e.applied) (t := e.clock), 
    a.allows_iff
  ]
  
theorem unprocessed_eq (e : s₁ ↓ᵉ s₂) : s₂.unprocessed = s₁.unprocessed \ {e.rcn} := by
  ext i
  simp [State.unprocessed, Equivalent.obj?_rcn_eq e.equiv, and_assoc, e.progress_eq]
  intro _; simp [Set.insert]; push_neg; simp [and_comm]

theorem rcn_mem_unprocessed (e : s₁ ↓ᵉ s₂) : e.rcn ∈ s₁.unprocessed := 
  ⟨e.allows_rcn.mem, e.allows_rcn.unprocessed⟩ 

theorem unprocessed_ssubset (e : s₁ ↓ᵉ s₂) : s₂.unprocessed ⊂ s₁.unprocessed := by
  simp [e.unprocessed_eq, Set.ssubset_iff_subset_ne]
  exact e.rcn_mem_unprocessed

end Execution.Step.Exec

namespace Execution.Step.Exec

variable [Proper α] {s s₁ : State α} {rcn : Reaction}

theorem indep_restriction_eq  
    (e : s₁ ↓ᵉ s₂) (hi : e.rcn ≮[s₁.rtr]≯ i) (ho : s₁.rtr[.rcn][i] = some rcn) : 
    input.restriction s₁ rcn cpt = input.restriction s₂ rcn cpt := by 
  simp [input.restriction]
  apply Partial.ext_restrict 
  intro d hd
  exact e.applied_rtr_eq ▸ e.apply.preserves_unchanged $ State.target_not_mem_indep_output ho hi hd

theorem indep_input_eq 
    (e : s₁ ↓ᵉ s₂) (hi : e.rcn ≮[s₁.rtr]≯ i) (h₁ : s₁.rtr[.rcn][i] = some rcn)
    (h₂ : s₂.rtr[.rcn][i] = some rcn) : s₁.input i = s₂.input i := by 
  simp [input, h₁, h₂]
  refine ⟨?_, e.preserves_tag⟩
  ext1
  exact e.indep_restriction_eq hi h₁

theorem indep_output_eq (e : s₁ ↓ᵉ s₂) (hi : e.rcn ≮[s₁.rtr]≯ i) : s₁.output i = s₂.output i := by 
  simp [output]
  have he := Equivalent.obj?_rcn_eq e.equiv
  cases h : s₁.rtr[.rcn][i] <;> simp [he ▸ h]
  simp [e.indep_input_eq hi h $ he ▸ h]

theorem indep_comm 
    (e₁ : s ↓ᵉ s₁) (e₁₂ : s₁ ↓ᵉ s₁₂) (e₂ : s ↓ᵉ s₂) (e₂₁ : s₂ ↓ᵉ s₂₁) 
    (hr₁ : e₁.rcn = e₂₁.rcn) (hr₂ : e₂.rcn = e₁₂.rcn) (hi : e₁.rcn ≮[s.rtr]≯ e₂.rcn) : 
    s₁₂ ≈ s₂₁ := by 
  have ho₁ := e₁.indep_output_eq hi
  have ho₂ := e₂.indep_output_eq hi.symm
  cases e₁; cases e₁₂; cases e₂; cases e₂₁
  case _ rcn₁ s₁ t₁ _ _ a₁ ht₁ rcn₂ s₁₂ t₁₂ _ _ a₁₂ ht₁₂ _ s₂ t₂ _ _ a₂ ht₂ _ s₂₁ t₂₁ _ _ a₂₁ ht₂₁ => 
    cases hr₁; cases hr₂; simp [Exec.rcn] at *
    have ⟨z₁₂, f₁₂⟩ := Apply.RTC.construct s₁ (s.output rcn₂)
    have ⟨z₂₁, f₂₁⟩ := Apply.RTC.construct s₂ (s.output rcn₁)
    rw [←ho₁] at a₁₂; rw [←ho₂] at a₂₁
    sorry 
    -- cases f₁₂.comm_record a₁₂; cases f₂₁.comm_record a₂₁
    -- rw [record_comm]; congr
    -- exact Apply.RTC.disjoint_targets_comm (s.indep_output_disjoint_targets hi) a₁ f₁₂ a₂ f₂₁

theorem indep_triggers_iff (e : s₁ ↓ᵉ s₂) (hi : i ≮[s₁.rtr]≯ e.rcn) : 
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
