import ReactorModel.Objects.Reactor.Raw
import ReactorModel.Objects.Reactor.ReactorType.Wellformed
import ReactorModel.Objects.Reactor.ReactorType.Updatable

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

-- Note: From this we get `ReactorType.Extensional Reactor` and `ReactorType.Indexable Reactor`.
instance : LawfulCoe Reactor Reactor.Raw where
  coe := Reactor.raw

noncomputable instance : Updatable Reactor where
  update rtr cmp i f := {
    raw := Updatable.update rtr.raw cmp i f
    wf  := Wellformed.equiv (LawfulUpdatable.lawful (α := Reactor.Raw) rtr cmp i f).equiv rtr.wf
  }

-- Note: From this we get `ReactorType.LawfulUpdatable Reactor`.
instance : LawfulUpdatableCoe Reactor Reactor.Raw where

theorem wellformed (rtr : Reactor) : Wellformed rtr :=
  rtr.wf.lift (rtr := rtr)

-- We add these definitions so that we can use dot-notation on `Reactor`s later. Type classes don't
-- support this notation yet.
abbrev ports (rtr : Reactor) := ReactorType.ports rtr
abbrev acts  (rtr : Reactor) := ReactorType.acts rtr
abbrev state (rtr : Reactor) := ReactorType.state rtr
abbrev rcns  (rtr : Reactor) := ReactorType.rcns rtr
abbrev nest  (rtr : Reactor) := ReactorType.nest rtr

noncomputable def scheduledTags (rtr : Reactor) : Set Time.Tag := 
  { g | ∃ i a, (rtr[.act][i] = some a) ∧ (g ∈ a.keys) }

end Reactor