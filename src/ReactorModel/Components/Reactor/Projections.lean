import ReactorModel.Components.Lift

open Classical Port

namespace Reactor

-- Lifted versions of the trivially liftable projections of `Raw.Reactor`.
def ports (rtr : Reactor) : ID ▸ Port             := rtr.raw.ports
def acts  (rtr : Reactor) : ID ▸ Time.Tag ▸ Value := rtr.raw.acts
def state (rtr : Reactor) : ID ▸ Value            := rtr.raw.state

-- The `nest` projection lifted to return a finmap of "proper" reactors.
-- 
-- We're doing two lifting steps at once here:
-- 1. We turn `rtr.raw.nest` into a finmap that has raw reactors as values.
-- 2. We map on that finmapto get a finmap that returns "proper" reactors (using `Reactor.fromRaw`).
def nest (rtr : Reactor) : ID ▸ Reactor := 
  let raw : Finmap ID (Raw.Reactor) := { lookup := rtr.raw.nest, finite := rtr.rawWF.direct.nestFiniteRtrs }
  raw.attach.map (λ ⟨_, h⟩ => Reactor.fromRaw _ (by
      have ⟨_, hm⟩ := Finmap.values_def.mp h
      have h' := Raw.Reactor.Ancestor.nested hm
      exact Raw.Reactor.Ancestor.preserves_wf h' rtr.rawWF
    )
  )  

theorem RawEquiv.nest (rtr : Reactor) : Finmap.forall₂' Reactor.RawEquiv rtr.nest rtr.raw.nest := {
  eqIDs := by
    intro i
    simp only [Reactor.nest, Finmap.map_mem_ids, Finmap.attach_mem_ids]
    exact Finmap.ids_def,
  rel := by
    intro i r r' hr hr'
    simp only [nest] at hr
    have ⟨⟨m, hm⟩, ⟨h₁, h₂⟩⟩ := Finmap.map_def hr
    simp at h₂
    have h := RawEquiv.fromRaw' h₂.symm
    have h₁ := Finmap.attach_def h₁
    simp at h h₁
    simp [h₁] at hr'
    simp [←hr', h]
}

theorem nest_mem_raw_iff {rtr rtr' : Reactor} {i} : rtr.nest i = rtr' ↔ rtr.raw.nest i = rtr'.raw := by
  constructor
  case mp =>
    intro h
    have ⟨hi, hv⟩ := RawEquiv.nest rtr
    have hm : i ∈ rtr.nest.ids := Finmap.ids_def'.mpr ⟨rtr', h.symm⟩
    have ⟨_, hx⟩ := Option.ne_none_iff_exists.mp $ (hi i).mp hm
    have he := hv h hx.symm
    simp [←hx, he.equiv]
  case mpr =>
    intro h
    have ⟨hi, hv⟩ := RawEquiv.nest rtr
    have hi := (hi i).mpr (Option.ne_none_iff_exists.mpr ⟨rtr'.raw, h.symm⟩)
    have ⟨x, hx⟩ := Finmap.ids_def'.mp hi
    have he := hv hx.symm h
    simp [←hx]
    exact Reactor.raw_ext_iff.mpr he.equiv  

-- The `rcns` projection lifted to return a finmap of "proper" reactions.
-- 
-- We're doing two lifting steps at once here:
-- 1. We turn `rtr.raw.rcns` into a finmap that has raw reactions as values.
-- 2. We map on that finmap to get a finmap that returns "proper" reactions (using `Reaction.fromRaw`).
def rcns (rtr : Reactor) : ID ▸ Reaction :=
  let raw : Finmap ID (Raw.Reaction) := { lookup := rtr.raw.rcns, finite := rtr.rawWF.direct.rcnsFinite }
  raw.attach.map $ λ ⟨_, h⟩ => Reaction.fromRaw rtr.rawWF (Finmap.values_def.mp h)
  
theorem RawEquiv.rcns (rtr : Reactor) : Finmap.forall₂' Reaction.RawEquiv rtr.rcns rtr.raw.rcns := {
  eqIDs := by
    intro i
    simp only [Reactor.rcns, Finmap.map_mem_ids, Finmap.attach_mem_ids]
    exact Finmap.ids_def
  rel := by
    intro i r r' hr hr'
    simp [rcns] at hr
    have ⟨⟨m, hm⟩, ⟨h₁, h₂⟩⟩ := Finmap.map_def hr
    have h := Reaction.RawEquiv.fromRaw' h₂.symm
    have h₁ := Finmap.attach_def h₁
    simp at h₁
    simp [h₁] at hr'
    simp [←hr', h]
}

theorem rcns_has_raw {rtr : Reactor} {rcn i} (h : rtr.rcns i = some rcn) : 
  ∃ raw, rtr.raw.rcns i = some raw := by
  have h' := Option.ne_none_iff_exists.mpr ⟨rcn, h.symm⟩
  simp only [rcns, ←Finmap.ids_def, Finmap.map_mem_ids, Finmap.attach_mem_ids] at h'
  have he := RawEquiv.rcns rtr
  have hi := (he.eqIDs _).mp h'
  simp only [Finmap.ids_def'] at h'
  have ⟨raw, hr⟩ := h'
  exact ⟨raw, hr.symm⟩

-- A projection for ports, that allows us to separate them by port role.
noncomputable def ports' (rtr : Reactor) (r : Port.Role) : ID ▸ Port := 
  rtr.ports.filter' (·.role = r)

noncomputable def portVals (rtr : Reactor) (r : Port.Role) : ID ▸ Value := 
  (rtr.ports' r).map Port.val

-- A direct projection to a reactor's normal reactions.
noncomputable def norms (rtr : Reactor) : ID ▸ Reaction :=
  rtr.rcns.filter' (Reaction.isNorm)

-- A direct projection to a reactor's mutations.
noncomputable def muts (rtr : Reactor) : ID ▸ Reaction :=
  rtr.rcns.filter' (Reaction.isMut)  

-- The set of all IDs that identify (input and output) ports of
-- reactors immediately (and not transitively) nested in a given reactor.
-- In other words, all port IDs appearing "one layer down".
-- 
-- This property is quite specific, but is required to nicely state properties
-- like `Reactor.wfNormDeps`.
noncomputable def nestedPortIDs (rtr : Reactor) (r : Port.Role) : Finset ID :=
  let description := { i | ∃ n ∈ rtr.nest.values, i ∈ (n.ports' r).ids }
  let finite : description.finite := by
    let f : Finset ID := rtr.nest.values.bUnion (λ n => (n.ports' r).ids)
    suffices h : description ⊆ ↑f 
      from Set.finite.subset (Finset.finite_to_set _) h
    simp [Set.subset_def]
  finite.toFinset

noncomputable def inputForRcn (σ : Reactor) (rcn : Reaction) (g : Time.Tag) : Reaction.Input := {
  portVals := (σ.portVals Role.in).restrict $ rcn.deps Role.in,
  acts := (σ.acts.filterMap (· g)).restrict $ rcn.deps Role.in,
  state := σ.state,
  time := g
}

noncomputable def scheduledTags (σ : Reactor) : Finset Time.Tag := 
  σ.acts.values.bUnion (·.ids)

-- TODO (maybe): Factor out the overlap between the proofs of `rcns_ext` and `nest_ext`.

theorem rcns_ext {rtr₁ rtr₂ : Reactor} (h : rtr₁.rcns = rtr₂.rcns) : rtr₁.raw.rcns = rtr₂.raw.rcns := by
  funext i
  have h₁ :=  RawEquiv.rcns rtr₁
  have h₁₁ := RawEquiv.rcns rtr₁
  have h₂ :=  RawEquiv.rcns rtr₂
  have h₂₂ := RawEquiv.rcns rtr₂
  cases hc : rtr₁.raw.rcns i
  case h.none =>
    rw [h] at h₁
    have h₁' := mt (h₁.eqIDs i).mp 
    simp only [Ne.def, not_not] at h₁'
    have h₂' := mt (h₂.eqIDs i).mpr $ h₁' hc
    simp only [Ne.def, not_not] at h₂'
    simp [h₂']
  case h.some rcn =>
    rw [←h] at h₂
    have h₁' := (h₁.eqIDs i).mpr
    simp only [Option.ne_none_iff_exists] at h₁'
    have h₁' := h₁' ⟨rcn, hc.symm⟩
    simp only [Finmap.ids_def'] at h₁'
    have ⟨x, hx⟩ := h₁'
    rw [h] at h₁
    have h₂' := (h₁.eqIDs i).mpr
    simp only [Option.ne_none_iff_exists] at h₂'
    have h₂' := h₂' ⟨rcn, hc.symm⟩
    have h₂₂' := Option.ne_none_iff_exists.mp $ (h₂₂.eqIDs i).mp h₂'
    have ⟨y, hy⟩ := h₂₂'
    rw [←hy]
    have hr₁ := h₁₁.rel hx.symm hc
    have hr₂ := h₂.rel hx.symm hy.symm
    simp [Reaction.RawEquiv.unique hr₁ hr₂]

theorem nest_ext {rtr₁ rtr₂ : Reactor} (h : rtr₁.nest = rtr₂.nest) : rtr₁.raw.nest = rtr₂.raw.nest := by
  funext i
  have h₁ :=  RawEquiv.nest rtr₁
  have h₁₁ := RawEquiv.nest rtr₁
  have h₂ :=  RawEquiv.nest rtr₂
  have h₂₂ := RawEquiv.nest rtr₂
  cases hc : rtr₁.raw.nest i
  case h.none =>
    rw [h] at h₁
    have h₁' := mt (h₁.eqIDs i).mp 
    simp only [Ne.def, not_not] at h₁'
    have h₂' := mt (h₂.eqIDs i).mpr $ h₁' hc
    simp only [Ne.def, not_not] at h₂'
    simp [h₂']
  case h.some rcn =>
    rw [←h] at h₂
    have h₁' := (h₁.eqIDs i).mpr
    simp only [Option.ne_none_iff_exists] at h₁'
    have h₁' := h₁' ⟨rcn, hc.symm⟩
    simp only [Finmap.ids_def'] at h₁'
    have ⟨x, hx⟩ := h₁'
    rw [h] at h₁
    have h₂' := (h₁.eqIDs i).mpr
    simp only [Option.ne_none_iff_exists] at h₂'
    have h₂' := h₂' ⟨rcn, hc.symm⟩
    have h₂₂' := Option.ne_none_iff_exists.mp $ (h₂₂.eqIDs i).mp h₂'
    have ⟨y, hy⟩ := h₂₂'
    rw [←hy]
    have hr₁ := h₁₁.rel hx.symm hc
    have hr₂ := h₂.rel hx.symm hy.symm
    simp [Reactor.RawEquiv.unique hr₁ hr₂]

theorem ext_iff {rtr₁ rtr₂ : Reactor} : 
  rtr₁ = rtr₂ ↔ 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts  ∧ 
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns  = rtr₂.rcns ∧ 
  rtr₁.nest  = rtr₂.nest := by
  constructor
  case mp =>
    intro h
    simp [ports, acts, state, raw_ext_iff.mp h]
    constructor <;> simp only [Finmap.ext, h]
  case mpr =>
    intro h
    apply raw_ext_iff.mpr
    apply Raw.Reactor.ext
    simp [ports, acts, state] at h
    simp only [h]
    have ⟨_, _, _, h₁, h₂⟩ := h
    simp [rcns_ext h₁, nest_ext h₂]

@[ext]
theorem ext {rtr₁ rtr₂ : Reactor} : 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts  ∧ 
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns  = rtr₂.rcns ∧ 
  rtr₁.nest  = rtr₂.nest → 
  rtr₁ = rtr₂ :=
  λ h => ext_iff.mpr h

end Reactor