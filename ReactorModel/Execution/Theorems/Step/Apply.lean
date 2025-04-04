import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.State

noncomputable section
open Reactor Execution State

namespace Execution.Step.Apply

variable [Hierarchical α] {s s₁ s₁' s₂ s₂' s₁₂ s₂₁ : State α} {c : Change α}

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

theorem events_congr (e : s₁ -[c]→ s₂) (e' : s₁' -[c]→ s₂') (he : s₁.events = s₁'.events) :
    s₂.events = s₂'.events := by
  cases e <;> cases e' <;> simp [he]
  exact schedule_events_congr he

theorem allows_iff (e : s₁ -[c]→ s₂) : s₁.Allows i ↔ s₂.Allows i :=
  Allows.congr e.equiv e.preserves_progress

end Execution.Step.Apply

namespace Execution.Step.Apply

variable [Readable α] {s s₁ s₂ : State α} {c : Change α}

theorem rtr_congr (e : s₁ -[c]→ s₂) (e' : s₁' -[c]→ s₂')
    (h : s₁.rtr = s₁'.rtr) : s₂.rtr = s₂'.rtr := by
  cases e <;> cases e' <;> simp [State.schedule_preserves_rtr, h]
  all_goals rw [h] at *; exact LawfulUpdate.unique ‹_› ‹_›

theorem comm_record (e₁ : s -[c]→ s₁) (e₂ : (s.record rcn) -[c]→ s₂) : s₁.record rcn = s₂ := by
  ext1
  case rtr      => exact e₁.rtr_congr e₂ (s.record_preserves_rtr rcn)
  case tag      => simp [record_preserves_tag, ←e₁.preserves_tag, ←e₂.preserves_tag]
  case progress => simp [record_progress_eq, ←e₂.preserves_progress, e₁.preserves_progress]
  case events   => exact e₁.events_congr e₂ (s.record_preserves_events rcn)

theorem deterministic (e₁ : s -[c]→ s₁) (e₂ : s -[c]→ s₂) : s₁ = s₂ := by
  cases e₁ <;> cases e₂ <;> simp <;> exact LawfulUpdate.unique ‹_› ‹_›

end Execution.Step.Apply

namespace Execution.Step.Apply

variable [Proper α] {c₁ c₂ : Change α} {s s₁ s₂ s₁₂ s₂₁ : State α}

theorem ne_target_comm (ht : c₁.target ≠ c₂.target ∨ c₁.target = none) (e₁ : s -[c₁]→ s₁)
    (e₁₂ : s₁ -[c₂]→ s₁₂) (e₂ : s -[c₂]→ s₂) (e₂₁ : s₂ -[c₁]→ s₂₁) : s₁₂ = s₂₁ := by
  cases e₁ <;> cases e₁₂ <;> cases e₂ <;> cases e₂₁ <;> simp [Change.target] at ht ⊢
  case act.act.act.act =>               exact schedule_ne_comm ht
  case inp.act.act.inp u₁ _ _ _ _ u₂ => cases LawfulUpdate.unique u₁ u₂; rfl
  case out.act.act.out u₁ _ _ _ _ u₂ => cases LawfulUpdate.unique u₁ u₂; rfl
  case stv.act.act.stv u₁ _ _ _ _ u₂ => cases LawfulUpdate.unique u₁ u₂; rfl
  case act.inp.inp.act u₁ _ u₂       => cases LawfulUpdate.unique u₁ u₂; rfl
  case act.out.out.act u₁ _ u₂       => cases LawfulUpdate.unique u₁ u₂; rfl
  case act.stv.stv.act u₁ _ u₂       => cases LawfulUpdate.unique u₁ u₂; rfl
  all_goals
    try exact LawfulUpdate.unique ‹_› ‹_›
    try case _ u₁ _ _ _ u₂ _ u₃ _ u₄ => exact LawfulUpdate.ne_comm u₁ u₂ u₃ u₄ <| by simp [ht]

-- TODO: Formalize this a bit nicer. Add an `apply` function to `State` when `Proper α`.
--       Also, this doesn't actually require `Proper` does it? If you trim down the requirements,
--       this could have implications on the generality of the progress theorem.
open Updatable in
def construct (s : State α) : (c : Change α) → (s' : State α) × (s -[c]→ s')
  | .inp i v   => ⟨{ s with rtr := update s.rtr .inp i v }, inp <| LawfulUpdatable.lawful ..⟩
  | .out i v   => ⟨{ s with rtr := update s.rtr .out i v }, out <| LawfulUpdatable.lawful ..⟩
  | .stv i v   => ⟨{ s with rtr := update s.rtr .stv i v }, stv <| LawfulUpdatable.lawful ..⟩
  | .act i t v => ⟨s.schedule i t v, act⟩
  | .mut _     => ⟨s, «mut»⟩

end Execution.Step.Apply

namespace Execution.Step.Apply.RTC

variable [Hierarchical α] {s₁ : State α} {out : Reaction.Output α}

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
    (e : s₁ -[out]→ s₂) (h : out.Forall (¬·.Targets cpt i)) : s₁.rtr[cpt][i] = s₂.rtr[cpt][i] := by
  induction e
  case refl => rfl
  case trans e _ hi =>
    have ⟨hh, ht⟩ := List.forall_cons _ _ _ |>.mp h
    exact e.preserves_unchanged hh ▸ hi ht

theorem preserves_independent (e : s₁ -[out]→ s₂) (h : rcn₁ ≮[s₁.rtr]≯ rcn₂) :
    rcn₁ ≮[s₂.rtr]≯ rcn₂ :=
  h.equiv e.equiv

theorem allows_iff (e : s₁ -[out]→ s₂) : s₁.Allows i ↔ s₂.Allows i := by
  induction e
  case refl => rfl
  case trans e _ hi => exact e.allows_iff.trans hi

end Execution.Step.Apply.RTC

namespace Execution.Step.Apply.RTC

variable [Readable α] {s s₁ s₂ : State α} {out : Reaction.Output α}

theorem comm_record (e₁ : s -[out]→ s₁) (e₂ : (s.record rcn) -[out]→ s₂) : s₁.record rcn = s₂ := by
  induction e₁ <;> cases e₂
  case refl.refl => rfl
  case trans.trans e₁ _ hi _ e₂ e₂' => exact hi <| (e₁.comm_record e₂).symm ▸ e₂'

theorem deterministic (e₁ : s -[out]→ s₁) (e₂ : s -[out]→ s₂) : s₁ = s₂ := by
  induction e₁ generalizing s₂ <;> cases e₂
  case refl.refl => rfl
  case trans.trans e₁ _ hi _ e₂ e₂' => exact hi <| (e₁.deterministic e₂) ▸ e₂'

end Execution.Step.Apply.RTC

namespace Execution.Step.Apply.RTC

variable [Proper α] {s s₁ s₂ s₁₂ s₂₁ : State α} {c : Change α} {out out₁ out₂ : Reaction.Output α}

def construct (s : State α) : (out : Reaction.Output α) → (s' : State α) × (s -[out]→ s')
  | []       => ⟨s, refl⟩
  | hd :: tl => let ⟨s', e⟩ := Apply.construct s hd; let ⟨_, e'⟩ := construct s' tl; ⟨_, trans e e'⟩

theorem ne_targets_comm_apply
    (ht : ∀ {t}, c.target = some t → t ∉ out.targets) (eₒ : s -[out]→ sₒ) (eₒ₁ : sₒ -[c]→ sₒ₁)
    (e₁ : s -[c]→ s₁) (e₁ₒ : s₁ -[out]→ s₁ₒ) : sₒ₁ = s₁ₒ := by
  induction eₒ generalizing s₁ <;> cases e₁ₒ
  case refl.refl => exact eₒ₁.deterministic e₁
  case trans.trans hd _ s' tl _ eₒ _ hi _ e₁ₒ e₁ₒ' =>
    have h : hd.target ≠ c.target ∨ hd.target = none := by
      by_contra hc
      push_neg at hc
      have ⟨_, h⟩ := Option.ne_none_iff_exists.mp hc.right
      exact ht (hc.left ▸ h.symm) <| Reaction.Output.target_mem_targets (by simp) h.symm
    have ⟨_, e'⟩ := Apply.construct s' c
    cases Apply.ne_target_comm h eₒ e' e₁ e₁ₒ
    exact hi (ht · <| Reaction.Output.mem_targets_cons ·) ‹_› ‹_› ‹_›

theorem disjoint_targets_comm
    (ht : Disjoint out₁.targets out₂.targets) (e₁ : s -[out₁]→ s₁) (e₁₂ : s₁ -[out₂]→ s₁₂)
    (e₂ : s -[out₂]→ s₂) (e₂₁ : s₂ -[out₁]→ s₂₁) : s₁₂ = s₂₁ := by
  induction e₁ generalizing s₂ <;> cases e₁₂ <;> cases e₂ <;> cases e₂₁
  case refl.refl.refl.refl => rfl
  case trans.trans.trans.trans hd₁ s z₁ tl₁ _ e₁ e₁' hd₂ _ tl₂ hi e₂ e₂' _ f₂ f₂' _ f₁ f₁' =>
    have h₁ : ∀ {t}, hd₁.target = some t → ¬t ∈ Reaction.Output.targets (hd₂ :: tl₂) := by
      intro _ h hm₂
      have hm₁ := Reaction.Output.target_mem_targets (out := hd₁ :: tl₁) (by simp) h
      exact absurd rfl <| Set.disjoint_iff_forall_ne.mp ht hm₁ hm₂
    have h₂ : Disjoint tl₁.targets <| Reaction.Output.targets (hd₂ :: tl₂) := by
      simp [Set.disjoint_iff_forall_ne]
      intro _ _ hm₁ _ _ hm₂ h₁ h₂
      subst h₁ h₂
      exact Set.disjoint_left.mp ht (Reaction.Output.mem_targets_cons hm₁) hm₂
    have ⟨_, g₁⟩ := Apply.RTC.construct z₁ (hd₂ :: tl₂)
    cases ne_targets_comm_apply h₁ (trans f₂ f₂') f₁ e₁ g₁
    exact hi h₂ (.trans e₂ e₂') g₁ f₁'
  case' refl.trans.trans.refl e₁ e₁' _ e₂ e₂' => skip
  case' trans.refl.refl.trans e₁ e₁' _ _ e₂ e₂' => skip
  all_goals cases e₁.deterministic e₂; exact e₁'.deterministic e₂'

end Execution.Step.Apply.RTC
