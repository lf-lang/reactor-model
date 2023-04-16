import ReactorModel.Objects.Reactor.Finite

namespace ReactorType

variable [Finite α] {rtr : α}

theorem mem_ids_iff {i} : (i ∈ Finite.ids rtr cpt) ↔ (∃ o, rtr[cpt][i] = some o) := by
  simp [Finite.ids, ←Partial.mem_def, Partial.mem_iff]

end ReactorType