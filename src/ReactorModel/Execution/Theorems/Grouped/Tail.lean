import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.Grouped.Instantaneous

open ReactorType

namespace Execution.Grouped

inductive Tail [Indexable α] : State α → State α → Type
  | none : Tail s s
  | some : (s₁ ↓ᵢ+ s₂) → Tail s₁ s₂

namespace Tail

theorem preserves_tag [Indexable α] {s₁ s₂ : State α} : (Tail s₁ s₂) → s₁.tag = s₂.tag
  | none => rfl
  | some e => e.preserves_tag

theorem deterministic [Readable α] {s s₁ s₂ : State α} (hp : s₁.progress = s₂.progress) :
    (Tail s s₁) → (Tail s s₂) → s₁ = s₂
  | none, none                  => rfl
  | some e₁, some e₂            => e₁.deterministic e₂ (e₁.preserves_tag ▸ e₂.preserves_tag) hp
  | none, some e | some e, none => e.progress_ne (by simp [hp]) |>.elim 

end Execution.Grouped.Tail