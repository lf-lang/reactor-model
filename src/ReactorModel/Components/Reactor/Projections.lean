import ReactorModel.Components.Lift

open Classical

variable {ι υ} [Value υ]

namespace Reactor

-- Lifted versions of the trivially liftable projections of `Raw.Reactor`.
def ports (rtr : Reactor ι υ) : ι ▸ υ          := rtr.raw.ports
def roles (rtr : Reactor ι υ) : ι ▸ Port.Role := rtr.raw.roles
def acts  (rtr : Reactor ι υ) : ι ▸ Time ▸ υ   := rtr.raw.acts
def state (rtr : Reactor ι υ) : ι ▸ υ          := rtr.raw.state
def prios (rtr : Reactor ι υ) : PartialOrder ι := rtr.raw.prios

-- The `nest` projection lifted to return a finmap of "proper" reactors.
-- 
-- We're doing two lifting steps at once here:
-- 1. We turn `rtr.raw.nest` into a finmap that has raw reactors as values.
-- 2. We map on that finmapto get a finmap that returns "proper" reactors (using `Reactor.fromRaw`).
def nest (rtr : Reactor ι υ) : ι ▸ Reactor ι υ := 
  let raw : Finmap ι (Raw.Reactor ι υ) := { lookup := rtr.raw.nest, finite := rtr.rawWF.direct.nestFiniteRtrs }
  raw.attach.map (λ ⟨_, h⟩ => Reactor.fromRaw _ (by
      have ⟨_, hm⟩ := Finmap.values_def.mp h
      have h' := Raw.Reactor.isAncestorOf.nested hm
      exact Raw.Reactor.isAncestorOf_preserves_wf h' rtr.rawWF
    )
  )

theorem nest_rawEquiv (rtr : Reactor ι υ) : Finmap.forall₂' Reactor.rawEquiv rtr.nest rtr.raw.nest := {
  eqIDs := by
    intro i
    simp only [nest, Finmap.map_mem_ids, Finmap.attach_mem_ids]
    exact Finmap.ids_def,
  rel := by
    intro i r r' hr hr'
    simp only [nest] at hr
    obtain ⟨⟨m, hm⟩, ⟨h₁, h₂⟩⟩ := Finmap.map_def hr
    simp at h₂
    have h := fromRaw_rawEquiv (Eq.symm h₂)
    have h₁ := Finmap.attach_def h₁
    simp at h h₁
    simp [h₁] at hr'
    simp [←hr', h]
}

theorem nest_mem_raw_iff {rtr rtr' : Reactor ι υ} {i} : rtr.nest i = rtr' ↔ rtr.raw.nest i = rtr'.raw := by
  apply Iff.intro
  case mp =>
    intro h
    obtain ⟨hi, hv⟩ := nest_rawEquiv rtr
    have hm : i ∈ rtr.nest.ids := by
      simp only [Finmap.ids_def, Option.ne_none_iff_exists]
      exact ⟨rtr', Eq.symm h⟩
    obtain ⟨_, hx⟩ := Option.ne_none_iff_exists.mp $ (hi i).mp hm
    have he := hv h (Eq.symm hx)
    simp only [rawEquiv] at he
    simp [←hx, he]
  case mpr =>
    intro h
    obtain ⟨hi, hv⟩ := nest_rawEquiv rtr
    have hi := (hi i).mpr (Option.ne_none_iff_exists.mpr ⟨rtr'.raw, Eq.symm h⟩)
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp (Finmap.ids_def.mp hi)
    have he := hv (Eq.symm hx) h
    simp only [rawEquiv] at he
    simp [←hx]
    exact Reactor.raw_ext_iff.mpr he     

-- The `rcns` projection lifted to return a finmap of "proper" reactions.
-- 
-- We're doing two lifting steps at once here:
-- 1. We turn `rtr.raw.rcns` into a finmap that has raw reactions as values.
-- 2. We map on that finmap to get a finmap that returns "proper" reactions (using `Reaction.fromRaw`).
def rcns (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  let raw : Finmap ι (Raw.Reaction ι υ) := { lookup := rtr.raw.rcns, finite := rtr.rawWF.direct.rcnsFinite }
  raw.attach.map $ λ ⟨_, h⟩ => Reaction.fromRaw rtr.rawWF (Finmap.values_def.mp h)
  
theorem rcns_rawEquiv (rtr : Reactor ι υ) : Finmap.forall₂' Reaction.rawEquiv rtr.rcns rtr.raw.rcns := {
  eqIDs := by
    intro i
    simp only [rcns, Finmap.map_mem_ids, Finmap.attach_mem_ids]
    exact Finmap.ids_def
  rel := by
    intro i r r' hr hr'
    simp [rcns] at hr
    obtain ⟨⟨m, hm⟩, ⟨h₁, h₂⟩⟩ := Finmap.map_def hr
    have h := Reaction.fromRaw_rawEquiv (Eq.symm h₂)
    have h₁ := Finmap.attach_def h₁
    simp at h₁
    simp [h₁] at hr'
    simp [←hr', h]
}

theorem rcns_has_raw {rtr : Reactor ι υ} {rcn i} (h : rtr.rcns i = some rcn) : 
  ∃ raw, rtr.raw.rcns i = some raw := by
  have h' := Option.ne_none_iff_exists.mpr ⟨rcn, Eq.symm h⟩
  simp only [rcns, ←Finmap.ids_def, Finmap.map_mem_ids, Finmap.attach_mem_ids] at h'
  have he := rcns_rawEquiv rtr
  have hi := (he.eqIDs _).mp h'
  simp only [Finmap.ids_def, Option.ne_none_iff_exists] at h'
  obtain ⟨raw, hr⟩ := h'
  exact ⟨raw, Eq.symm hr⟩

-- A projection for ports, that allows us to separate them by port role.
noncomputable def ports' (rtr : Reactor ι υ) (r : Port.Role) : ι ▸ υ := 
  rtr.ports.filter (λ i => rtr.roles i = r)

-- A direct projection to a reactor's normal reactions.
noncomputable def norms (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isNorm)

-- A direct projection to a reactor's mutations.
noncomputable def muts (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isMut)  

-- The set of all IDs that identify (input and output) ports of
-- reactors immediately (and not transitively) nested in a given reactor.
-- In other words, all port IDs appearing "one layer down".
-- 
-- This property is quite specific, but is required to nicely state properties
-- like `Reactor.wfNormDeps`.
noncomputable def nestedPortIDs (rtr : Reactor ι υ) (r : Port.Role) : Finset ι :=
  let description := {i | ∃ n ∈ rtr.nest.values, i ∈ (n.ports' r).ids}
  let finite : description.finite := by
    let f : Finset ι := rtr.nest.values.bUnion (λ n => (n.ports' r).ids)
    suffices h : description ⊆ ↑f 
      from Set.finite.subset (Finset.finite_to_set _) h
    simp [Set.subset_def]
  finite.toFinset

theorem ext_iff {rtr₁ rtr₂ : Reactor ι υ} : 
  rtr₁ = rtr₂ ↔ 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.roles = rtr₂.roles ∧
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns  = rtr₂.rcns ∧
  rtr₁.nest  = rtr₂.nest  ∧ rtr₁.prios = rtr₂.prios := by
  apply Iff.intro
  case mp =>
    intro h
    simp [ports, roles, state, prios, raw_ext_iff.mp h]
    apply And.intro <;> (sorry)
  case mpr =>
    intro h
    apply raw_ext_iff.mpr
    apply Raw.Reactor.ext
    simp [ports, roles, state, prios] at h
    simp [h]
    obtain ⟨_, _, _, h₁, h₂, _⟩ := h
    clear h
    apply And.intro <;>
    sorry

@[ext]
theorem ext {rtr₁ rtr₂ : Reactor ι υ} : 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.roles = rtr₂.roles ∧
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns  = rtr₂.rcns ∧
  rtr₁.nest  = rtr₂.nest  ∧ rtr₁.prios = rtr₂.prios →
  rtr₁ = rtr₂ :=
  λ h => ext_iff.mpr h

end Reactor