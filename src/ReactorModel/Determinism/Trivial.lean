import ReactorModel.Determinism.ExecutionStep

namespace Execution

abbrev State.Trivial (s : State) : Prop := 
  s.rtr[.rcn].ids = ∅

theorem State.Trivial.of_not_Nontrivial (h : ¬Nontrivial s) : s.Trivial := by
  by_contra hc; exact h ⟨Set.nonempty_iff_ne_empty.mpr hc⟩

theorem State.Nontrivial.not_Trivial (h : Nontrivial s) : ¬s.Trivial :=
  h.nontrivial.ne_empty

section

variable {s₁ : State} (triv : s₁.Trivial)

theorem State.Advance.preserves_Trivial : (Advance s₁ s₂) → s₂.Trivial
  | mk .. => triv

theorem AdvanceTag.preserves_Trivial (a : s₁ ⇓- s₂) : s₂.Trivial :=
  a.advance.preserves_Trivial triv

theorem ClosedExecution.preserves_Trivial {e : s₁ ⇓| s₂} : s₂.Trivial := by
  simp [State.Trivial, ←e.preserves_rcns, triv]

theorem Step.preserves_Trivial : (s₁ ⇓ s₂) → s₂.Trivial
  | close e   => e.preserves_Trivial triv
  | advance a => a.preserves_Trivial triv

theorem InstStep.not_Trivial (e : s₁ ⇓ᵢ s₂) : ¬s₁.Trivial :=
  s₁.operation_some_to_Nontrivial e.wfOp |>.not_Trivial

theorem InstExecution.trivial_eq : (s₁ ⇓ᵢ* s₂) → s₁ = s₂
  | refl      => rfl
  | trans e _ => absurd triv e.not_Trivial 

theorem ClosedExecution.trivial_eq (e : s₁ ⇓| s₂) : s₁ = s₂ :=
  e.exec.trivial_eq triv

end

inductive AdvanceTag.RTC : State → State → Type
  | refl : RTC s s
  | trans : (s₁ ⇓- s₂) → (RTC s₂ s₃) → RTC s₁ s₃   

def to_AdvanceTagRTC (triv : s₁.Trivial) : (s₁ ⇓* s₂) → AdvanceTag.RTC s₁ s₂
  | refl                 => .refl
  | step (.advance a) e' => .trans a (e'.to_AdvanceTagRTC $ a.preserves_Trivial triv)
  | step (.close e) e'   => e.trivial_eq triv ▸ (e'.to_AdvanceTagRTC $ e.preserves_Trivial triv)

theorem AdvanceTag.RTC.tag_le : (AdvanceTag.RTC s₁ s₂) → s₁.tag ≤ s₂.tag
  | refl       => le_refl _
  | trans a a' => le_trans (le_of_lt a.tag_lt) a'.tag_le

theorem AdvanceTag.RTC.deterministic (ht : s₁.tag = s₂.tag) : 
    (AdvanceTag.RTC s s₁) → (AdvanceTag.RTC s s₂) →  s₁ = s₂
  | refl,         refl         => rfl
  | refl,         trans a a'   => absurd ht      (ne_of_lt $ lt_of_lt_of_le a.tag_lt a'.tag_le)
  | trans a a',   refl         => absurd ht.symm (ne_of_lt $ lt_of_lt_of_le a.tag_lt a'.tag_le)
  | trans a₁ a₁', trans a₂ a₂' => a₁'.deterministic ht (a₂.determinisic a₁ ▸ a₂')

theorem trivial_deterministic 
    (triv : ¬s.Nontrivial) (e₁ : s ⇓* s₁) (e₂ : s ⇓* s₂) (ht : s₁.tag = s₂.tag) : s₁ = s₂ :=
  AdvanceTag.RTC.deterministic ht
    (e₁.to_AdvanceTagRTC $ .of_not_Nontrivial triv) 
    (e₂.to_AdvanceTagRTC $ .of_not_Nontrivial triv) 

end Execution