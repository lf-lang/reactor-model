import ReactorModel.Objects.Reactor.Core
import ReactorModel.Objects.Reactor.TypeClasses.Indexable

namespace Reactor

protected structure Raw where
  core : Reactor.Core
  uniqueIDs : ReactorType.UniqueIDs core

namespace Raw

open ReactorType in
instance : ReactorType Reactor.Raw where
  ports    := ports ∘ core
  acts     := acts  ∘ core
  state    := state ∘ core
  rcns     := rcns  ∘ core
  nest rtr := 
    (nest rtr.core).attach.map fun ⟨core, h⟩ => {
      core := core
      uniqueIDs := {
        allEq := fun l₁ l₂ => 
          by injection rtr.uniqueIDs.allEq (.nest h.choose_spec l₁) (.nest h.choose_spec l₂)
      }
    }

-- Note: From this we also get `ReactorType.Extensional Reactor.Raw`.
instance : ReactorType.Extensional.LawfulCoe Reactor.Raw Reactor.Core where
  coe := Reactor.Raw.core
  coe_ext_iff := by intro (mk ..) (mk ..); simp  

instance : ReactorType.Indexable Reactor.Raw where
  uniqueIDs := ReactorType.UniqueIDs.lift (β := Reactor.Core) $ Reactor.Raw.uniqueIDs ‹_› 

end Raw
end Reactor
