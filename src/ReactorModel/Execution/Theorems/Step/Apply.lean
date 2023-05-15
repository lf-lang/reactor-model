import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.State

open Classical ReactorType Execution State

namespace Execution.Step.Apply

variable [Indexable α] {s s₁ s₁' s₂ s₂' s₁₂ s₂₁ : State α} {c : Change}

theorem preserves_tag (e : s₁ -[c]→ s₂) : s₁.tag = s₂.tag := by
  cases e <;> simp [schedule_preserves_tag]

theorem preserves_progress (e : s₁ -[c]→ s₂) : s₁.progress = s₂.progress := by 
  cases e <;> simp [schedule_preserves_progress]

theorem equiv (e : s₁ -[c]→ s₂) : s₁.rtr ≈ s₂.rtr := by
  cases e
  case «mut» => exact .refl _
  case act => simp [schedule_preserves_rtr]; exact .refl _
  all_goals exact LawfulUpdate.equiv ‹_›

theorem preserves_unchanged (e : s₁ -[c]→ s₂) (h : ¬c.Targets cpt i) :
    s₁.rtr[cpt][i] = s₂.rtr[cpt][i] := by
  cases e <;> try exact .refl _
  all_goals simp [LawfulUpdate.obj?_preserved (Change.Targets.norm_not h) ‹_›]

theorem ne_target_comm {c₁ c₂ : Change} 
    (ht : c₁.target ≠ c₂.target ∨ c₁.target = none) (e₁ : s -[c₁]→ s₁) (e₁₂ : s₁ -[c₂]→ s₁₂) 
    (e₂ : s -[c₂]→ s₂) (e₂₁ : s₂ -[c₁]→ s₂₁) : s₁₂ = s₂₁ := by
  /-ext1 <;> cases_change c₁ <;> cases_change c₂ <;> simp [apply, Change.target] at *
  all_goals 
    try rfl
    try exact LawfulUpdatable.update_ne_comm $ by simp_all
  apply Partial.update_ne_comm _ ht
  -/
  sorry

theorem rtr_congr (e : s₁ -[c]→ s₂) (e' : s₁' -[c]→ s₂') 
    (h : s₁.rtr = s₁'.rtr) : s₂.rtr = s₂'.rtr := by 
  sorry

theorem events_congr (e : s₁ -[c]→ s₂) (e' : s₁' -[c]→ s₂') 
    (hr : s₁.rtr = s₁'.rtr) (he : s₁.events = s₁'.events) : s₂.events = s₂'.events := by 
  sorry

theorem comm_record (e₁ : s -[c]→ s₁) (e₂ : (s.record rcn) -[c]→ s₂) : s₁.record rcn = s₂ := by
  ext1
  case rtr      => exact e₁.rtr_congr e₂ (s.record_preserves_rtr rcn)
  case tag      => simp [record_preserves_tag, ←e₁.preserves_tag, ←e₂.preserves_tag]
  case progress => simp [record_progress_eq, ←e₂.preserves_progress, e₁.preserves_progress]
  case events   => exact e₁.events_congr e₂ (s.record_preserves_rtr rcn) (s.record_preserves_events rcn)

end Execution.Step.Apply

theorem Execution.Step.Apply.deterministic [Readable α] {s s₁ s₂ : State α} {c : Change} 
    (e₁ : s -[c]→ s₁) (e₂ : s -[c]→ s₂) : s₁ = s₂ := by
  cases e₁ <;> cases e₂ <;> simp <;> exact LawfulUpdate.unique ‹_› ‹_›

namespace Execution.Step.Apply.RTC

variable [Indexable α] {s₁ : State α} {c : Change} {out out₁ out₂ : Reaction.Output}

theorem preserves_tag (e : s₁ -[out]→ s₂) : s₁.tag = s₂.tag := by 
  induction e
  case refl => rfl
  case trans e _ hi => exact e.preserves_tag ▸ hi

theorem preserves_progress (e : s₁ -[out]→ s₂) : s₁.progress = s₂.progress := by 
  induction e
  case refl => rfl
  case trans e _ hi => exact e.preserves_progress ▸ hi

theorem equiv (e : s₁ -[out]→ s₂) : s₁.rtr ≈ s₂.rtr := by
  induction e
  case refl => exact .refl _
  case trans e _ hi => exact Equivalent.trans e.equiv hi

theorem preserves_unchanged {cpt : Component.Valued} 
    (e : s₁ -[out]→ s₂) (h : out.All₂ (¬·.Targets cpt i)) : s₁.rtr[cpt][i] = s₂.rtr[cpt][i] := by
  induction e
  case refl => rfl
  case trans e _ hi =>
    have ⟨hh, ht⟩ := List.all₂_cons _ _ _ |>.mp h
    exact e.preserves_unchanged hh ▸ hi ht 

theorem ne_targets_comm_apply 
    (ht : ∀ {t}, c.target = some t → t ∉ out.targets) (eₒ : s -[out]→ sₒ) (eₒ₁ : sₒ -[c]→ sₒ₁) 
    (e₁ : s -[c]→ s₁) (e₁ₒ : s₁ -[out]→ s₁ₒ) : sₒ₁ = s₁ₒ := by
  /-
  induction out generalizing s <;> simp [apply'] at *
  case cons hd tl hi =>
    suffices h : hd.target ≠ c.target ∨ hd.target = none by 
      rw [hi $ fun _ _ h hm => ht _ _ h $ List.mem_targets_cons hm, apply_ne_target_comm h]
    by_contra hc
    push_neg at hc
    have ⟨_, h⟩ := Option.ne_none_iff_exists.mp hc.right
    exact ht _ _ (hc.left ▸ h.symm) $ List.target_mem_targets (by simp) h.symm
  -/
  sorry

theorem disjoint_targets_comm 
    (ht : Disjoint out₁.targets out₂.targets) (e₁ : s -[out₁]→ s₁) (e₁₂ : s₁ -[out₂]→ s₁₂) 
    (e₂ : s -[out₂]→ s₂) (e₂₁ : s₂ -[out₁]→ s₂₁) : s₁₂ = s₂₁ := by
  /-
  induction cs₁ generalizing s <;> cases cs₂ <;> simp [apply'] at *
  case cons.cons hd₁ tl₁ hd₂ tl₂ hi =>
    have h₁ : Disjoint (List.targets tl₁) (List.targets (hd₂ :: tl₂)) := by
      simp [Set.disjoint_iff_forall_ne]
      intro _ _ hm₁ _ _ hm₂ h₁ h₂
      subst h₁ h₂    
      exact Set.disjoint_left.mp ht (List.mem_targets_cons hm₁) hm₂
    have h₂ : hd₁.target ≠ hd₂.target ∨ hd₁.target = none := by
      by_contra hc
      push_neg at hc
      have ⟨_, h⟩ := Option.ne_none_iff_exists.mp hc.right
      have h₁ := (hd₁ :: tl₁).target_mem_targets (by simp) h.symm
      have h₂ := (hd₂ :: tl₂).target_mem_targets (by simp) (hc.left ▸ h.symm)
      exact Set.disjoint_left.mp ht h₁ h₂
    have h₃ : ∀ {t}, hd₁.target = some t → ¬t ∈ tl₂.targets := by
      intro _ h hm
      have h₁ := (hd₁ :: tl₁).target_mem_targets (by simp) h
      exact Set.disjoint_left.mp ht h₁ $ List.mem_targets_cons hm
    rw [hi h₁, apply_ne_target_comm h₂, ←apply', ←apply', ←ne_targets_comm_apply h₃]
    rfl
  -/
  sorry

theorem comm_record (e₁ : s -[out]→ s₁) (e₂ : (s.record rcn) -[out]→ s₂) : s₁.record rcn = s₂ := by
  induction e₁ <;> cases e₂
  case refl.refl => rfl
  case trans.trans e₁ _ hi _ e₂ e₂' => exact hi $ (e₁.comm_record e₂).symm ▸ e₂'

end Execution.Step.Apply.RTC

theorem Execution.Step.Apply.RTC.deterministic 
    [Readable α] {s s₁ s₂ : State α} {out : Reaction.Output} 
    (e₁ : s -[out]→ s₁) (e₂ : s -[out]→ s₂) : s₁ = s₂ := by
  induction e₁ generalizing s₂ <;> cases e₂
  case refl.refl => rfl
  case trans.trans e₁ _ hi _ e₂ e₂' => exact hi $ (e₁.deterministic e₂) ▸ e₂'