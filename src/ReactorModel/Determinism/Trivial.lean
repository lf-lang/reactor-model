import ReactorModel.Determinism.ExecutionStep

open ReactorType Classical

variable [Proper α]

namespace Execution

variable {s s₁ : State α} in section

abbrev State.Trivial (s : State α) : Prop := 
  s.rtr[.rcn] = ∅

namespace State
namespace Trivial

theorem equiv {s₁ s₂ : State α} (e : s₁.rtr ≈ s₂.rtr) (t : s₁.Trivial) : s₂.Trivial :=
  Equivalent.obj?_rcn_eq e |>.symm.trans t

theorem of_not_nontrivial (h : ¬Nontrivial s) : s.Trivial :=
  byContradiction (h ⟨·⟩)

theorem closed (h : Trivial s) : s.Closed := by
  simp [Closed] -- TODO: We run into a problem here: `progress` might contain reactions that aren't
                --       in `s.rtr[.rcn]`. We might be able to circumvent this issue by changing the 
                --       definition of `Closed` to a `⊆` instead of `=`.
                --       Alternatives:
                --       * Change the definition of `State` to include this fact as a requirement.
                --       * Change the definition of `Progress` (the only place where this theorem is
                --         currently being used) to include this as a requirement.
  sorry

end Trivial
end State

variable (triv : s₁.Trivial) in section

namespace Instantaneous

theorem Step.not_Trivial (e : s₁ ⇓ᵢ s₂) : ¬s₁.Trivial := by
  by_contra ht
  simp [State.Trivial, Partial.empty_iff] at ht
  cases (Partial.mem_iff.mp e.allows_rcn.mem).choose_spec ▸ ht e.rcn  

theorem Execution.trivial_eq : (s₁ ⇓ᵢ+ s₂) → s₁ = s₂
  | single e | trans e _ => absurd triv e.not_Trivial 

theorem ClosedExecution.preserves_Trivial {e : s₁ ⇓| s₂} : s₂.Trivial := by
  simp [State.Trivial, ←Equivalent.obj?_rcn_eq e.equiv, triv]

theorem ClosedExecution.trivial_eq (e : s₁ ⇓| s₂) : s₁ = s₂ :=
  e.exec.trivial_eq triv

end Instantaneous

theorem State.Advance.preserves_Trivial : (Advance s₁ s₂) → s₂.Trivial
  | ⟨_, c⟩ => triv.equiv c.equiv

theorem AdvanceTag.preserves_Trivial (a : s₁ ⇓- s₂) : s₂.Trivial :=
  a.advance.preserves_Trivial triv

theorem Step.preserves_Trivial : (s₁ ⇓ s₂) → s₂.Trivial
  | close e   => e.preserves_Trivial triv
  | advance a => a.preserves_Trivial triv

end
end

namespace AdvanceTag 

inductive RTC : State α → State α → Prop
  | refl : RTC s s
  | trans : (s₁ ⇓- s₂) → (RTC s₂ s₃) → RTC s₁ s₃   

theorem RTC.tag_le {s₁ s₂ : State α} (a : AdvanceTag.RTC s₁ s₂) : s₁.tag ≤ s₂.tag := by
  induction a with
  | refl         => exact le_refl _
  | trans a _ hi => exact le_trans (le_of_lt a.tag_lt) hi

theorem RTC.deterministic {s s₁ s₂ : State α} 
    (ht : s₁.tag = s₂.tag) (a₁ : AdvanceTag.RTC s s₁) (a₂ : AdvanceTag.RTC s s₂) : s₁ = s₂ := by
  induction a₁ generalizing s₂ <;> cases a₂
  case refl.refl         => rfl
  case refl.trans a a'   => exact absurd ht      (ne_of_lt $ lt_of_lt_of_le a.tag_lt a'.tag_le)
  case trans.refl a a' _ => exact absurd ht.symm (ne_of_lt $ lt_of_lt_of_le a.tag_lt a'.tag_le)
  case trans.trans a₁ a₁' hi _ a₂ a₂' => exact hi ht (a₂.deterministic a₁ ▸ a₂')
  
end AdvanceTag

theorem to_advanceTagRTC {s₁ s₂ : State α} (triv : s₁.Trivial) (e : s₁ ⇓* s₂) : 
    AdvanceTag.RTC s₁ s₂ := by
  induction e <;> try cases ‹_ ⇓ _›
  case refl              => exact .refl  
  case step.advance hi a => exact .trans a (hi $ a.preserves_Trivial triv)
  case step.close hi e   => exact e.trivial_eq triv ▸ (hi $ e.preserves_Trivial triv)

theorem trivial_deterministic {s : State α}
    (triv : ¬s.Nontrivial) (e₁ : s ⇓* s₁) (e₂ : s ⇓* s₂) (ht : s₁.tag = s₂.tag) : s₁ = s₂ :=
  AdvanceTag.RTC.deterministic ht
    (e₁.to_advanceTagRTC $ .of_not_nontrivial triv) 
    (e₂.to_advanceTagRTC $ .of_not_nontrivial triv) 

end Execution