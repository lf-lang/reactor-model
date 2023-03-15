import ReactorModel.Objects.Reactor.Core
import ReactorModel.Objects.Reactor.ReactorType.Indexable

open Classical

namespace Reactor

protected structure Raw where
  core : Reactor.Core
  unique_ids : ReactorType.UniqueIDs core

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
      unique_ids := {
        allEq := fun l₁ l₂ => 
          by injection rtr.unique_ids.allEq (.nest h.choose_spec l₁) (.nest h.choose_spec l₂)
      }
    }

-- Note: From this we also get `ReactorType.Extensional Reactor.Raw`.
instance : ReactorType.LawfulCoe Reactor.Raw Reactor.Core where
  coe := Reactor.Raw.core

instance : ReactorType.Indexable Reactor.Raw where
  unique_ids := ReactorType.UniqueIDs.lift (β := Reactor.Core) $ Reactor.Raw.unique_ids ‹_› 

open ReactorType Updatable in
noncomputable instance : ReactorType.Updatable Reactor.Raw where
  update rtr cmp i f := {
    core := update rtr.core cmp i f
    unique_ids := UniqueIDs.updated (lawful (α := Reactor.Core) rtr cmp i f) rtr.unique_ids
  }
  lawful rtr cmp i f := by exact lawful (α := Reactor.Core) rtr cmp i f |>.lift

end Raw
end Reactor
