import ReactorModel.Objects.Reactor.Raw
import ReactorModel.Objects.Reactor.TypeClasses.Proper

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
instance : ReactorType.Extensional.LawfulCoe Reactor Reactor.Raw where
  coe := Reactor.raw
  coe_ext_iff := by intro (mk ..) (mk ..); simp

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
  { g | ∃ i a, (rtr[.act][i] = some a) ∧ (g ∈ a.dom) }

end Reactor