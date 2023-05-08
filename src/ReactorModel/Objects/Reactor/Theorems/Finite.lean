import ReactorModel.Objects.Reactor.Finite

theorem ReactorType.mem_ids_iff [Indexable α] [Finite α] {rtr : α} {i} : 
    (i ∈ Finite.ids rtr cpt) ↔ (∃ o, rtr[cpt][i] = some o) := by
  simp [Finite.ids, ←Partial.mem_def, Partial.mem_iff]