import ReactorModel.Objects.Reactor.Finite

theorem Reactor.mem_ids_iff [Hierarchical α] [Finite α] {rtr : α} {i} : 
    (i ∈ Finite.ids rtr cpt) ↔ (∃ o, rtr[cpt][i] = some o) := by
  simp [Finite.ids, ←Partial.mem_def, Partial.mem_iff]