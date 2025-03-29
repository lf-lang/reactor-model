import ReactorModel.Execution.Theorems.Grouped.Basic

open Classical Reactor

namespace Execution

variable [Proper α] {s : State α}

theorem deterministic
    (e₁ : Execution s s₁) (e₂ : Execution s s₂) (ht : s₁.tag = s₂.tag)
    (hp : s₁.progress = s₂.progress) : s₁ = s₂ :=
  e₁.toGrouped.deterministic ht hp e₂.toGrouped

-- Property (1) on page 10 of https://www.informatik.uni-bremen.de/agbs/jp/papers/trs_script.pdf.
theorem tag_le {s₁ s₂ : State α} : (Execution s₁ s₂) → s₁.tag ≤ s₂.tag
  | .refl        => le_refl _
  | .trans e₁ e₂ => e₁.tag_le.trans e₂.tag_le
