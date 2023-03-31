import ReactorModel.Determinism.ExecutionStep

open ReactorType Classical

variable [Indexable α]

namespace Execution

variable {s s₁ : State α} in section

abbrev State.Trivial (s : State α) : Prop := 
  s.rtr[.rcn] = ∅

theorem State.Trivial.of_not_Nontrivial (h : ¬Nontrivial s) : s.Trivial :=
  byContradiction (h ⟨·⟩)

variable (triv : s₁.Trivial) in section

namespace Instantaneous

theorem Step.not_Trivial (e : s₁ ⇓ᵢ s₂) : ¬s₁.Trivial := by
  by_contra ht
  simp [State.Trivial, Partial.empty_iff] at ht
  cases (Partial.mem_iff.mp e.allows_rcn.mem).choose_spec ▸ ht e.rcn  

theorem Execution.trivial_eq : (s₁ ⇓ᵢ* s₂) → s₁ = s₂
  | refl      => rfl
  | trans e _ => absurd triv e.not_Trivial 

theorem ClosedExecution.preserves_Trivial {e : s₁ ⇓| s₂} : s₂.Trivial := by
  simp [State.Trivial, ←Equivalent.obj?_rcn_eq e.equiv, triv]

theorem ClosedExecution.trivial_eq (e : s₁ ⇓| s₂) : s₁ = s₂ :=
  e.exec.trivial_eq triv

end Instantaneous

theorem State.Advance.preserves_Trivial : (Advance s₁ s₂) → s₂.Trivial
  | mk .. => triv

theorem AdvanceTag.preserves_Trivial (a : s₁ ⇓- s₂) : s₂.Trivial :=
  a.advance.preserves_Trivial triv

theorem Step.preserves_Trivial : (s₁ ⇓ s₂) → s₂.Trivial
  | close e   => e.preserves_Trivial triv
  | advance a => a.preserves_Trivial triv

end
end

namespace AdvanceTag 

inductive RTC : State α → State α → Type
  | refl : RTC s s
  | trans : (s₁ ⇓- s₂) → (RTC s₂ s₃) → RTC s₁ s₃   

theorem RTC.tag_le {s₁ s₂ : State α} : (AdvanceTag.RTC s₁ s₂) → s₁.tag ≤ s₂.tag
  | refl       => le_refl _
  | trans a a' => le_trans (le_of_lt a.tag_lt) a'.tag_le

theorem RTC.deterministic {s s₁ s₂ : State α} (ht : s₁.tag = s₂.tag) : 
    (AdvanceTag.RTC s s₁) → (AdvanceTag.RTC s s₂) → s₁ = s₂
  | refl,         refl         => rfl
  | refl,         trans a a'   => absurd ht      (ne_of_lt $ lt_of_lt_of_le a.tag_lt a'.tag_le)
  | trans a a',   refl         => absurd ht.symm (ne_of_lt $ lt_of_lt_of_le a.tag_lt a'.tag_le)
  | trans a₁ a₁', trans a₂ a₂' => a₁'.deterministic ht (a₂.determinisic a₁ ▸ a₂')

end AdvanceTag

def to_AdvanceTagRTC {s₁ s₂ : State α} (triv : s₁.Trivial) : (s₁ ⇓* s₂) → AdvanceTag.RTC s₁ s₂
  | refl                 => .refl
  | step (.advance a) e' => .trans a (e'.to_AdvanceTagRTC $ a.preserves_Trivial triv)
  | step (.close e) e'   => e.trivial_eq triv ▸ (e'.to_AdvanceTagRTC $ e.preserves_Trivial triv)

theorem trivial_deterministic {s : State α}
    (triv : ¬s.Nontrivial) (e₁ : s ⇓* s₁) (e₂ : s ⇓* s₂) (ht : s₁.tag = s₂.tag) : s₁ = s₂ :=
  AdvanceTag.RTC.deterministic ht
    (e₁.to_AdvanceTagRTC $ .of_not_Nontrivial triv) 
    (e₂.to_AdvanceTagRTC $ .of_not_Nontrivial triv) 

end Execution