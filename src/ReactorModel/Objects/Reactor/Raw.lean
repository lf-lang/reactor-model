import ReactorModel.Objects.Reactor.Core
import ReactorModel.Objects.Reactor.ReactorType.Indexable

noncomputable section
open Classical

namespace Reactor

protected structure Raw where
  core : Reactor.Core
  unique_ids : ReactorType.UniqueIDs core

namespace Raw

open ReactorType

instance : ReactorType Reactor.Raw where
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

-- Note: From this we get `ReactorType.Extensional` and `ReactorType.WellFounded`.
instance : LawfulCoe Reactor.Raw Reactor.Core where
  coe := Reactor.Raw.core

open Updatable LawfulUpdatable in
instance : Updatable Reactor.Raw where
  update rtr cmp i f := {
    core := update rtr.core cmp i f
    unique_ids := UniqueIDs.updated (lawful (α := Reactor.Core) rtr cmp i f) rtr.unique_ids
  }

-- Note: From this we get `ReactorType.LawfulUpdatable Reactor.Raw`.
instance : LawfulUpdatableCoe Reactor.Raw Reactor.Core where

instance : Indexable Reactor.Raw where
  unique_ids := UniqueIDs.lift (β := Reactor.Core) $ Reactor.Raw.unique_ids ‹_› 

end Raw
end Reactor
