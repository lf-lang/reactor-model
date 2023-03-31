import ReactorModel.Objects.Reactor.Instances.Raw

noncomputable section

structure Reactor where
  raw : Reactor.Raw
  wf  : ReactorType.Wellformed raw

namespace Reactor

open ReactorType

instance : ReactorType Reactor where
  ports    := ports ∘ raw
  acts     := acts  ∘ raw
  state    := state ∘ raw
  rcns     := rcns  ∘ raw
  nest rtr := 
    (nest rtr.raw).attach.map fun ⟨raw, h⟩ => { 
      raw := raw, 
      wf := rtr.wf.nested h.choose_spec 
    }

-- Note: From this we get `ReactorType.Extensional`, `ReactorType.WellFounded` and 
--       `ReactorType.Indexable`.
instance : LawfulCoe Reactor Reactor.Raw where
  coe := Reactor.raw

instance : Updatable Reactor where
  update rtr cpt i f := {
    raw := Updatable.update rtr.raw cpt i f
    wf  := Wellformed.equiv (LawfulUpdatable.lawful (α := Reactor.Raw) rtr cpt i f).equiv rtr.wf
  }

-- Note: From this we get `ReactorType.LawfulUpdatable Reactor`.
instance : LawfulUpdatableCoe Reactor Reactor.Raw where

instance : Proper Reactor where
  wellformed rtr := rtr.wf.lift (rtr := rtr)

end Reactor