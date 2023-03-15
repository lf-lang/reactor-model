import ReactorModel.Objects.Reactor.Raw
import ReactorModel.Objects.Reactor.ReactorType.Wellformed
import ReactorModel.Objects.Reactor.ReactorType.Updatable

structure Reactor where
  raw : Reactor.Raw
  wf  : ReactorType.Wellformed raw

namespace Reactor

open ReactorType in
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
instance : ReactorType.LawfulCoe Reactor Reactor.Raw where
  coe := Reactor.raw

-- TODO: Perhaps it would be useful to have two type classes:
-- (1) `Updatable` which only requires the `update` function.
-- (2) `LawfulUpdatable` which extends `Updatable` with the `lawful` property.
--
-- Then you should be able to do some automatic type class lifting via `LawfulCoe` again. Like:
-- `instance : [Updatable α] [LawfulUpdatable β] [LawfulCoe α β] : LawfulUpdatable α`.
-- This, you don't have to specify the `lawful` field below.
open ReactorType Updatable in
noncomputable instance : ReactorType.Updatable Reactor where
  update rtr cmp i f := {
    raw := update rtr.raw cmp i f
    wf  := Wellformed.updated (lawful (α := Reactor.Raw) rtr cmp i f) rtr.wf
  }
  lawful rtr cmp i f := by exact lawful (α := Reactor.Raw) rtr cmp i f |>.lift

theorem wellformed (rtr : Reactor) : ReactorType.Wellformed rtr :=
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