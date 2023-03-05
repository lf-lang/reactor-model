import ReactorModel.Objects.Reactor.Raw
import ReactorModel.Objects.Reactor.TypeClasses.Proper

open ReactorType in
structure Reactor where
  raw : Reactor.Raw
  private wf : Wellformed raw

namespace Reactor

def ports : Reactor → ID ⇀ Port             := (·.raw.ports)
def acts  : Reactor → ID ⇀ Time.Tag ⇀ Value := (·.raw.acts)
def state : Reactor → ID ⇀ Value            := (·.raw.state)
def rcns  : Reactor → ID ⇀ Reaction         := (·.raw.rcns)

def nest (rtr : Reactor) : ID ⇀ Reactor :=
  rtr.raw.nest.attach.map fun ⟨raw, h⟩ => { raw := raw, wf := rtr.wf.nested h.choose_spec }

private theorem nest_raw_comm (rtr : Reactor) : 
    rtr.raw.nest = rtr.nest.map Reactor.raw := by
  simp [nest, Partial.map_map, Function.comp, Partial.attach_map_val]

private theorem ext_iff_raw : {rtr₁ rtr₂ : Reactor} → (rtr₁ = rtr₂ ↔ rtr₁.raw = rtr₂.raw)
  | mk .., mk .. => by simp

theorem ext_iff {rtr₁ rtr₂ : Reactor} : 
    rtr₁ = rtr₂ ↔ 
    rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts ∧ rtr₁.state = rtr₂.state ∧ 
    rtr₁.rcns = rtr₂.rcns ∧ rtr₁.nest  = rtr₂.nest := by
  simp [ext_iff_raw, Reactor.Raw.ext_iff, ports, state, rcns, acts, nest_raw_comm]
  intros
  exact {
    mp := Partial.map_inj (by simp [Function.Injective, ext_iff_raw])
    mpr := by simp_all
  }

instance : ReactorType.Proper Reactor where
  ports      := Reactor.ports
  acts       := Reactor.acts
  state      := Reactor.state
  rcns       := Reactor.rcns
  nest       := Reactor.nest
  uniqueIDs  := sorry
  wellformed := sorry

noncomputable def scheduledTags (rtr : Reactor) : Set Time.Tag := 
  { g | ∃ i a, (rtr[.act][i] = some a) ∧ (g ∈ a.dom) }

end Reactor