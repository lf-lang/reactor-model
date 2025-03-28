import ReactorModel.Objects.Reactor.Finite
import ReactorModel.Objects.Reactor.Theorems.Hierarchical

namespace Reactor

variable [Hierarchical α] [Finite α] {rtr rtr₁ rtr₂ : α}

theorem mem_ids_iff : (i ∈ Finite.ids rtr cpt) ↔ (∃ o, rtr[cpt][i] = some o) := by
  simp [Finite.ids, ←Partial.mem_def, Partial.mem_iff]

def equiv_card_eq (e : rtr₁ ≈ rtr₂) (cpt : Component) : rtr₁#cpt = rtr₂#cpt := by
  simp only [Finite.card, Equivalent.ids_eq e]
