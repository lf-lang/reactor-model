import ReactorModel.Components.Lift

variable {ι υ} [ID ι] [Value υ]

namespace Reactor

def ports (rtr : Reactor ι υ) : Ports ι υ       := rtr.raw.ports
def roles (rtr : Reactor ι υ) : ι ▸ Ports.Role  := rtr.raw.roles
def state (rtr : Reactor ι υ) : StateVars ι υ   := rtr.raw.state
def prios (rtr : Reactor ι υ) : PartialOrder ι  := rtr.raw.prios

-- The `nest` accessor lifted to return a finmap of "proper" reactors.
-- 
-- We're doing two lifting steps at once here:
-- 1. We turn `rtr.raw.nest` into a finmap that has raw reactors as values.
-- 2. We map on that finmap to get a finmap that returns "proper" reactors.
def nest (rtr : Reactor ι υ) : ι ▸ Reactor ι υ := 
  let raw : Finmap ι (Raw.Reactor ι υ) := { lookup := rtr.raw.nest, finite := rtr.rawWF.direct.nestFiniteRtrs }
  raw.map' (λ _ h => Reactor.fromRaw _ (by
      have ⟨_, hm⟩ := Finmap.values_def.mp h
      have h' := Raw.Reactor.isAncestorOf.nested hm
      exact Raw.Reactor.isAncestorOf_preserves_wf h' rtr.rawWF
    )
  )

theorem nest_rawEquiv (rtr : Reactor ι υ) : Finmap.forall₂' Reactor.rawEquiv rtr.nest rtr.raw.nest := {
  eqIDs := by
    intro i
    simp only [nest, Finmap.map'_mem_ids]
    exact Finmap.ids_def,
  rel := by
    intro i r r' hr hr'
    simp [nest] at hr
    obtain ⟨m, hm, ⟨h₁, h₂⟩⟩ := Finmap.map'_def hr
    have h := fromRaw_rawEquiv (Eq.symm h₂)
    simp at h₁
    simp [h₁] at hr'
    simp [←hr', h]
}

theorem nest_rawEquiv' {rtr rtr' : Reactor ι υ} {i} (h : rtr.nest i = rtr') : rtr.raw.nest i = rtr'.raw := by
  obtain ⟨hi, hv⟩ := nest_rawEquiv rtr
  have hm : i ∈ rtr.nest.ids := by
    simp only [Finmap.ids_def, Option.ne_none_iff_exists]
    exact ⟨rtr', Eq.symm h⟩
  obtain ⟨_, hx⟩ := Option.ne_none_iff_exists.mp $ (hi i).mp hm
  have he := hv h (Eq.symm hx)
  simp only [rawEquiv] at he
  simp [←hx, he]

-- The `rcns` accessor lifted to return a finmap of "proper" reactions.
-- 
-- We're doing two lifting steps at once here:
-- 1. We turn `rtr.raw.rcns` into a finmap that has raw reactions as values.
-- 2. We map on that finmap to get a finmap that returns "proper" reactions.
def rcns (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  let raw : Finmap ι (Raw.Reaction ι υ) := { lookup := rtr.raw.rcns, finite := rtr.rawWF.direct.rcnsFinite }
  raw.map' $ λ _ h => Reaction.fromRaw rtr.rawWF (Finmap.values_def.mp h)
  
-- TODO: Show this and `nest_rawEquiv` using `Finmap.forall₂'_map'`.
theorem rcns_rawEquiv (rtr : Reactor ι υ) : Finmap.forall₂' Reaction.rawEquiv rtr.rcns rtr.raw.rcns := {
  eqIDs := by
    intro i
    simp only [rcns, Finmap.map'_mem_ids]
    exact Finmap.ids_def
  rel := by
    intro i r r' hr hr'
    simp [rcns] at hr
    obtain ⟨m, hm, ⟨h₁, h₂⟩⟩ := Finmap.map'_def hr
    have h := Reaction.fromRaw_rawEquiv (Eq.symm h₂)
    simp at h₁
    simp [h₁] at hr'
    simp [←hr', h]
}

theorem rcns_has_raw {rtr : Reactor ι υ} {rcn i} (h : rtr.rcns i = some rcn) : 
  ∃ raw, rtr.raw.rcns i = some raw := by
  have h' := Option.ne_none_iff_exists.mpr ⟨rcn, Eq.symm h⟩
  simp only [rcns, ←Finmap.ids_def, Finmap.map'_mem_ids] at h'
  have he := rcns_rawEquiv rtr
  have hi := (he.eqIDs _).mp h'
  simp only [Finmap.ids_def, Option.ne_none_iff_exists] at h'
  obtain ⟨raw, hr⟩ := h'
  exact ⟨raw, Eq.symm hr⟩

-- An accessor for ports, that allows us to separate them by port role.
noncomputable def ports' (rtr : Reactor ι υ) : Ports.Role → Ports ι υ := rtr.raw.ports'

noncomputable def norms (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isNorm)

noncomputable def muts (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isMut)  

noncomputable def nestedPortIDs (rtr : Reactor ι υ) (r : Ports.Role) : Finset ι :=
  let description := {i | ∃ n ∈ rtr.nest.values, i ∈ (n.ports' r).ids}
  let finite : description.finite := by
    let f : Finset ι := rtr.nest.values.bUnion (λ n => (n.ports' r).ids)
    suffices h : description ⊆ ↑f 
      from Set.finite.subset (Finset.finite_to_set _) h
    simp [Set.subset_def]
  finite.toFinset

end Reactor