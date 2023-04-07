import ReactorModel.Objects.Reactor.Proper
import ReactorModel.Objects.Reactor.Theorems.Basic
import ReactorModel.Objects.Reactor.Theorems.Accessible
import ReactorModel.Objects.Reactor.Theorems.WellUpdatable

namespace ReactorType

-- TODO: Why do you need to provide some fields explicitly for the following instances?

instance [Proper α] : Accessible α where
  unique_ids := Proper.unique_ids

instance [Proper α] : WellUpdatable α where
  wf := Proper.wf

namespace Wellformed

open Indexable Equivalent
variable [Indexable α] {rtr₁ : α}

scoped macro "equiv_local_proof " dep:ident : term => 
  `($dep $ mem_get?_iff (obj?_rtr_equiv ‹_› ‹_› ‹_›) |>.mp ‹_›)

set_option hygiene false in
scoped macro "equiv_nested_proof " dep:ident : term => `(
  fun hc hp => 
    have e        := obj?_rtr_equiv ‹_› h₁ h₂
    have ⟨_, hc'⟩ := get?_some_iff e |>.mp ⟨_, hc⟩ 
    $dep hc' $ (mem_get?_iff $ get?_rtr_some_equiv e hc hc').mp hp
)

theorem ValidDependency.equiv 
    (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][j] = some con₁) (h₂ : rtr₂[.rtr][j] = some con₂) : 
    (ValidDependency con₁ rk dk d) → ValidDependency con₂ rk dk d
  | inp h           => equiv_local_proof inp
  | out h           => equiv_local_proof out
  | stv h           => equiv_local_proof stv
  | act h           => equiv_local_proof act
  | nestedIn  hc hp => (equiv_nested_proof nestedIn) hc hp
  | nestedOut hc hp => (equiv_nested_proof nestedOut) hc hp

theorem equiv (e : rtr₁ ≈ rtr₂) (wf : Wellformed rtr₁) : Wellformed rtr₂ where
  unique_inputs h₁ h₂ := 
    wf.unique_inputs (e.obj?_rcn_eq.symm ▸ h₁) (e.obj?_rcn_eq.symm ▸ h₂)
  ordered_prio h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩ 
    have e := obj?_rtr_equiv ‹_› h₁' h₁
    ordered_prio ‹_› h₁' (get?_rcn_eq e ▸ h₂) (get?_rcn_eq e ▸ h₃)
  valid_deps h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩ 
    have e := obj?_rtr_equiv ‹_› h₁' h₁
    wf.valid_deps h₁' (get?_rcn_eq e ▸ h₂) h₃ |>.equiv ‹_› h₁' h₁

theorem nested (wf : Wellformed rtr₁) (h : get? rtr₁ .rtr i = some rtr₂) : Wellformed rtr₂ where
  unique_inputs h₁ h₂ := wf.unique_inputs (obj?_some_nested h h₁) (obj?_some_nested h h₂)
  ordered_prio h₁     := wf.ordered_prio (obj?_some_nested' h h₁).choose_spec
  valid_deps h₁       := wf.valid_deps (obj?_some_nested' h h₁).choose_spec
  
end Wellformed
end ReactorType