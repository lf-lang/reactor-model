import ReactorModel.Objects.Reactor.Raw
import ReactorModel.Objects.Reactor.TypeClasses.Proper

open ReactorType in
structure Reactor where
  raw : Reactor.Raw
  wf  : Wellformed raw

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

noncomputable def scheduledTags (rtr : Reactor) : Set Time.Tag := 
  { g | ∃ i a, (rtr[.act][i] = some a) ∧ (g ∈ a.dom) }

end Reactor