import ReactorModel.Objects.Reactor.Instances.Core
import ReactorModel.Objects.Reactor.Theorems

noncomputable section
open Classical

namespace Reactor

protected structure Raw where
  core : Reactor.Core
  unique_ids : Reactor.UniqueIDs core

namespace Raw

open Reactor

instance : Reactor Reactor.Raw where
  ports    := ports ∘ core
  acts     := acts  ∘ core
  state    := state ∘ core
  rcns     := rcns  ∘ core
  nest rtr := 
    (nest rtr.core).attach.map fun ⟨core, h⟩ => {
      core := core
      unique_ids.allEq := fun l₁ l₂ => by 
        injection rtr.unique_ids.allEq (.nest h.choose_spec l₁) (.nest h.choose_spec l₂)
    }

-- Note: From this we get `Reactor.Extensional` and `Reactor.WellFounded`.
instance : LawfulCoe Reactor.Raw Reactor.Core where
  coe := Reactor.Raw.core

open Updatable LawfulUpdatable in
instance : Updatable Reactor.Raw where
  update rtr cpt i f := {
    core := update rtr.core cpt i f
    unique_ids := UniqueIDs.updated (lawful (α := Reactor.Core) rtr cpt i f) rtr.unique_ids
  }

-- Note: From this we get `Reactor.LawfulUpdatable Reactor.Raw`.
instance : LawfulUpdatableCoe Reactor.Raw Reactor.Core where

instance : Indexable Reactor.Raw where
  unique_ids := UniqueIDs.lift (β := Reactor.Core) $ Reactor.Raw.unique_ids ‹_› 

end Raw
end Reactor
