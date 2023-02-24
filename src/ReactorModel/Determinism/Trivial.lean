import ReactorModel.Determinism.ExecutionStep

namespace Execution

theorem InstStep.not_Trivial (e : s₁ ⇓ᵢ s₂) : ¬(State.Trivial s₁) :=
  s₁.operation_some_to_Nontrivial e.wfOp |>.not_Trivial

theorem InstExecution.trivial_eq [State.Trivial s₁] : (s₁ ⇓ᵢ* s₂) → s₁ = s₂
  | refl => rfl
  | trans e _ => absurd (inferInstanceAs s₁.Trivial) e.not_Trivial 

instance AdvanceTag.preserves_Trivial [State.Trivial s₁] {e : s₁ ⇓- s₂} : State.Trivial s₂ :=
  match e with | ⟨_, _⟩ => inferInstance

instance ClosedExecution.preserves_Trivial [State.Trivial s₁] {e : s₁ ⇓| s₂} : 
    State.Trivial s₂ where
  trivial := e.preserves_rcns ▸ State.Trivial.trivial

theorem ClosedExecution.trivial_eq [State.Trivial s₁] (e : s₁ ⇓| s₂) : s₁ = s₂ :=
  e.exec.trivial_eq

instance Step.preserves_Trivial [State.Trivial s₁] : (s₁ ⇓ s₂) → State.Trivial s₂
  | close e => e.preserves_Trivial
  | advance a => a.preserves_Trivial

inductive AdvanceTag.RTC : State → State → Type
  | refl : RTC s s
  | trans : (s₁ ⇓- s₂) → (RTC s₂ s₃) → RTC s₁ s₃   

theorem AdvanceTag.RTC.deterministic 
  (a₁ : AdvanceTag.RTC s s₁) (a₂ : AdvanceTag.RTC s s₂) (ht : s₁.tag = s₂.tag) : s₁ = s₂ := by
  induction a₁ <;> cases a₂
  case refl.refl                       => rfl
  case' refl.trans a _, trans.refl _ a => exact absurd ht a.tag_ne
  case trans.trans a₁ _ hi _ a₂ c₂     => exact hi (a₂.determinisic a₁ ▸ c₂) ht

def to_AdvanceTagRTC [State.Trivial s₁] : (s₁ ⇓* s₂) → AdvanceTag.RTC s₁ s₂
  | refl => .refl
  | step (.advance a) e' => 
    have := a.preserves_Trivial -- TODO: Make this work via type class inference.
    .trans a e'.to_AdvanceTagRTC
  | step (.close e) e' => 
    have := e.preserves_Trivial -- TODO: Make this work via type class inference.
    e.trivial_eq ▸ e'.to_AdvanceTagRTC

theorem trivial_deterministic [trivial : State.Trivial s] 
    (e₁ : s ⇓* s₁) (e₂ : s ⇓* s₂) (ht : s₁.tag = s₂.tag) : s₁ = s₂ :=
  e₁.to_AdvanceTagRTC.deterministic e₂.to_AdvanceTagRTC ht

end Execution