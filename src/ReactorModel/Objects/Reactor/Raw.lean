import ReactorModel.Objects.Reactor.Core

namespace Reactor

protected structure Raw where
  core : Reactor.Core
  private coreUniqueIDs : ∀ {cmp i} (l₁ l₂ : Lineage cmp i core), l₁ = l₂ 

namespace Raw

protected def ports : Reactor.Raw → ID ⇀ Port             := (·.core.ports)
protected def acts  : Reactor.Raw → ID ⇀ Time.Tag ⇀ Value := (·.core.acts)
protected def state : Reactor.Raw → ID ⇀ Value            := (·.core.state)
protected def rcns  : Reactor.Raw → ID ⇀ Reaction         := (·.core.rcns)

protected def nest (rtr : Reactor.Raw) : ID ⇀ Reactor.Raw :=
  rtr.core.nest.attach.map fun ⟨core, h⟩ => {
    core := core
    coreUniqueIDs := by
      intro _ _ l₁ l₂
      injection rtr.coreUniqueIDs (.nest h.choose_spec l₁) (.nest h.choose_spec l₂)
  }

private theorem nest_core_comm (rtr : Reactor.Raw) : 
    rtr.core.nest = rtr.nest.map Raw.core := by
  simp [Raw.nest, Partial.map_map, Function.comp, Partial.attach_map_val]

private theorem ext_iff_core : {rtr₁ rtr₂ : Reactor.Raw} → (rtr₁ = rtr₂ ↔ rtr₁.core = rtr₂.core)
  | mk .., mk .. => by simp

theorem ext_iff {rtr₁ rtr₂ : Reactor.Raw} : 
    rtr₁ = rtr₂ ↔ 
    rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts ∧ rtr₁.state = rtr₂.state ∧ 
    rtr₁.rcns = rtr₂.rcns ∧ rtr₁.nest  = rtr₂.nest := by
  simp [ext_iff_core, Reactor.Core.ext_iff, Raw.ports, Raw.state, Raw.rcns, Raw.acts, nest_core_comm]
  intros
  exact {
    mp := Partial.map_inj (by simp [Function.Injective, ext_iff_core])
    mpr := by simp_all
  }

instance : ReactorType.Indexable Reactor.Raw where
  ports     := Reactor.Raw.ports
  acts      := Reactor.Raw.acts
  state     := Reactor.Raw.state
  rcns      := Reactor.Raw.rcns
  nest      := Reactor.Raw.nest
  uniqueIDs := sorry

end Raw
end Reactor
