import ReactorModel.Objects.Reactor.Core
import ReactorModel.Objects.Reactor.TypeClasses.Indexable

namespace Reactor

open ReactorType in
protected structure Raw where
  core : Reactor.Core
  uniqueIDs : ∀ {cmp i} (l₁ l₂ : Lineage cmp i core), l₁ = l₂ 

namespace Raw

open ReactorType in
instance : ReactorType Reactor.Raw where
  ports    := ports ∘ core
  acts     := acts  ∘ core
  state    := state ∘ core
  rcns     := rcns  ∘ core
  nest rtr := 
    nest rtr.core |>.attach.map fun ⟨core, h⟩ => {
      core := core
      uniqueIDs := by
        intro _ _ l₁ l₂
        injection rtr.uniqueIDs (.nest h.choose_spec l₁) (.nest h.choose_spec l₂)
    }

instance : ReactorType.Indexable Reactor.Raw where
  uniqueIDs := sorry

-- Note: From this we get `ReactorType.Extensional Reactor.Raw`.
instance : ReactorType.Extensional.LawfulCoe Reactor.Raw Reactor.Core where
  coe := Reactor.Raw.core
  coe_ext_iff := by intro (mk ..) (mk ..); simp  

end Raw
end Reactor
