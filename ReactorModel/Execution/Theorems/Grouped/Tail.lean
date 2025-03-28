import ReactorModel.Execution.Basic
import ReactorModel.Execution.Theorems.Grouped.Instantaneous

open Reactor

namespace Execution.Grouped

inductive Tail [Hierarchical α] : State α → State α → Type
  | none : Tail s s
  | some : (s₁ ↓ᵢ+ s₂) → Tail s₁ s₂

namespace Tail

variable [Hierarchical α] {s₁ s₂ : State α}

def length : (Tail s₁ s₂) → Nat
  | none   => 0
  | some e => e.length

def length_le [Reactor.Finite α] {s₁ s₂ : State α} : (e : Tail s₁ s₂) → e.length ≤ s₁.rtr#.rcn + 1
  | none   => by simp [length]
  | some e => e.length_le_rcns_card.trans (Nat.le_succ _)

theorem preserves_tag  : (Tail s₁ s₂) → s₁.tag = s₂.tag
  | none   => rfl
  | some e => e.preserves_tag

theorem closed_to_none (h : s₁.Closed) : (Tail s₁ s₂) → s₁ = s₂
  | none   => rfl
  | some e => absurd h e.not_closed

end Tail

theorem Tail.deterministic [Proper α] {s s₁ s₂ : State α} (hp : s₁.progress = s₂.progress) :
    (Tail s s₁) → (Tail s s₂) → s₁ = s₂
  | none, none                  => rfl
  | some e₁, some e₂            => e₁.deterministic e₂ hp
  | none, some e | some e, none => e.progress_ne (by simp [hp]) |>.elim

end Execution.Grouped
