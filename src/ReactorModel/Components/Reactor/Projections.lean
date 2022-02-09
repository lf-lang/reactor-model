import ReactorModel.Components.Lift

open Classical Port

variable {ι υ} [Value υ]

namespace Reactor

-- Lifted versions of the trivially liftable projections of `Raw.Reactor`.
def ports (rtr : Reactor ι υ) : ι ▸ υ            := rtr.raw.ports
def roles (rtr : Reactor ι υ) : ι ▸ Port.Role    := rtr.raw.roles
def acts  (rtr : Reactor ι υ) : ι ▸ Time.Tag ▸ υ := rtr.raw.acts
def state (rtr : Reactor ι υ) : ι ▸ υ            := rtr.raw.state
def prios (rtr : Reactor ι υ) : PartialOrder ι   := rtr.raw.prios

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

theorem RawEquiv.nest (rtr : Reactor ι υ) : Finmap.forall₂' Reactor.RawEquiv rtr.nest rtr.raw.nest := {
  eqIDs := by
    intro i
    simp only [Reactor.nest, Finmap.map_mem_ids, Finmap.attach_mem_ids]
    exact Finmap.ids_def,
  rel := by
    intro i r r' hr hr'
    simp only [nest] at hr
    obtain ⟨⟨m, hm⟩, ⟨h₁, h₂⟩⟩ := Finmap.map_def hr
    simp at h₂
    have h := RawEquiv.fromRaw' $ Eq.symm h₂
    have h₁ := Finmap.attach_def h₁
    simp at h h₁
    simp [h₁] at hr'
    simp [←hr', h]
}

theorem nest_mem_raw_iff {rtr rtr' : Reactor ι υ} {i} : rtr.nest i = rtr' ↔ rtr.raw.nest i = rtr'.raw := by
  constructor
  case mp =>
    intro h
    obtain ⟨hi, hv⟩ := nest_rawEquiv rtr
    have hm : i ∈ rtr.nest.ids := Finmap.ids_def'.mp ⟨rtr', Eq.symm h⟩
    obtain ⟨_, hx⟩ := Option.ne_none_iff_exists.mp $ (hi i).mp hm
    have he := hv h (Eq.symm hx)
    simp [←hx, he.equiv]
  case mpr =>
    intro h
    obtain ⟨hi, hv⟩ := nest_rawEquiv rtr
    have hi := (hi i).mpr (Option.ne_none_iff_exists.mpr ⟨rtr'.raw, Eq.symm h⟩)
    obtain ⟨x, hx⟩ := Finmap.ids_def'.mp hi
    have he := hv (Eq.symm hx) h
    simp [←hx]
    exact Reactor.raw_ext_iff.mpr he.equiv  

-- The `rcns` projection lifted to return a finmap of "proper" reactions.
-- 
-- We're doing two lifting steps at once here:
-- 1. We turn `rtr.raw.rcns` into a finmap that has raw reactions as values.
-- 2. We map on that finmap to get a finmap that returns "proper" reactions (using `Reaction.fromRaw`).
def rcns (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  let raw : Finmap ι (Raw.Reaction ι υ) := { lookup := rtr.raw.rcns, finite := rtr.rawWF.direct.rcnsFinite }
  raw.attach.map $ λ ⟨_, h⟩ => Reaction.fromRaw rtr.rawWF (Finmap.values_def.mp h)
  
theorem RawEquiv.rcns (rtr : Reactor ι υ) : Finmap.forall₂' Reaction.RawEquiv rtr.rcns rtr.raw.rcns := {
  eqIDs := by
    intro i
    simp only [Reactor.rcns, Finmap.map_mem_ids, Finmap.attach_mem_ids]
    exact Finmap.ids_def
  rel := by
    intro i r r' hr hr'
    simp [rcns] at hr
    obtain ⟨⟨m, hm⟩, ⟨h₁, h₂⟩⟩ := Finmap.map_def hr
    have h := Reaction.RawEquiv.fromRaw' $ Eq.symm h₂
    have h₁ := Finmap.attach_def h₁
    simp at h₁
    simp [h₁] at hr'
    simp [←hr', h]
}

theorem rcns_has_raw {rtr : Reactor ι υ} {rcn i} (h : rtr.rcns i = some rcn) : 
  ∃ raw, rtr.raw.rcns i = some raw := by
  have h' := Option.ne_none_iff_exists.mpr ⟨rcn, Eq.symm h⟩
  simp only [rcns, ←Finmap.ids_def, Finmap.map_mem_ids, Finmap.attach_mem_ids] at h'
  have he := RawEquiv.rcns rtr
  have hi := (he.eqIDs _).mp h'
  simp only [Finmap.ids_def'] at h'
  obtain ⟨raw, hr⟩ := h'
  exact ⟨raw, Eq.symm hr⟩

-- A projection for ports, that allows us to separate them by port role.
noncomputable def ports' (rtr : Reactor ι υ) (r : Port.Role) : ι ▸ υ := 
  rtr.ports.filter (λ i => rtr.roles i = r)

set_option quotPrecheck false in
notation i₁:max " <[" σ "] " i₂:max => (@LT.lt _ $ @Preorder.toLT _ $ @PartialOrder.toPreorder _ $ Reactor.prios σ) i₁ i₂

def predecessors (σ : Reactor ι υ) (rcn : ι) : Set ι :=
 { rcn' ∈ σ.rcns.ids | rcn' <[σ] rcn }

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

noncomputable def inputForRcn (σ : Reactor ι υ) (rcn : Reaction ι υ) (t : Time.Tag) : Reaction.Input ι υ := {
  ports := σ.ports.restrict $ rcn.deps Role.in,
  acts := (σ.acts.filterMap (· t)).restrict $ rcn.deps Role.in,
  state := σ.state
}

noncomputable def scheduledTags (σ : Reactor ι υ) : Finset Time.Tag := 
  σ.acts.values.bUnion (·.ids)

-- TODO (maybe): Factor out the overlap between the proofs of `rcns_ext` and `nest_ext`.

theorem rcns_ext {rtr₁ rtr₂ : Reactor ι υ} (h : rtr₁.rcns = rtr₂.rcns) : rtr₁.raw.rcns = rtr₂.raw.rcns := by
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
    have h₁' := h₁' ⟨rcn, Eq.symm hc⟩
    simp only [Finmap.ids_def'] at h₁'
    obtain ⟨x, hx⟩ := h₁'
    rw [h] at h₁
    have h₂' := (h₁.eqIDs i).mpr
    simp only [Option.ne_none_iff_exists] at h₂'
    have h₂' := h₂' ⟨rcn, Eq.symm hc⟩
    have h₂₂' := Option.ne_none_iff_exists.mp $ (h₂₂.eqIDs i).mp h₂'
    obtain ⟨y, hy⟩ := h₂₂'
    rw [←hy]
    have hr₁ := h₁₁.rel (Eq.symm hx) hc
    have hr₂ := h₂.rel (Eq.symm hx) (Eq.symm hy)
    simp [Reaction.RawEquiv.unique hr₁ hr₂]

theorem nest_ext {rtr₁ rtr₂ : Reactor ι υ} (h : rtr₁.nest = rtr₂.nest) : rtr₁.raw.nest = rtr₂.raw.nest := by
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
    have h₁' := h₁' ⟨rcn, Eq.symm hc⟩
    simp only [Finmap.ids_def'] at h₁'
    obtain ⟨x, hx⟩ := h₁'
    rw [h] at h₁
    have h₂' := (h₁.eqIDs i).mpr
    simp only [Option.ne_none_iff_exists] at h₂'
    have h₂' := h₂' ⟨rcn, Eq.symm hc⟩
    have h₂₂' := Option.ne_none_iff_exists.mp $ (h₂₂.eqIDs i).mp h₂'
    obtain ⟨y, hy⟩ := h₂₂'
    rw [←hy]
    have hr₁ := h₁₁.rel (Eq.symm hx) hc
    have hr₂ := h₂.rel (Eq.symm hx) (Eq.symm hy)
    simp [Reactor.RawEquiv.unique hr₁ hr₂]

theorem ext_iff {rtr₁ rtr₂ : Reactor ι υ} : 
  rtr₁ = rtr₂ ↔ 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.roles = rtr₂.roles ∧
  rtr₁.acts = rtr₂.acts   ∧ rtr₁.state = rtr₂.state ∧ 
  rtr₁.rcns  = rtr₂.rcns  ∧ rtr₁.nest  = rtr₂.nest  ∧ 
  rtr₁.prios = rtr₂.prios := by
  constructor
  case mp =>
    intro h
    simp [ports, roles, acts, state, prios, raw_ext_iff.mp h]
    constructor <;> simp only [Finmap.ext, h]
  case mpr =>
    intro h
    apply raw_ext_iff.mpr
    apply Raw.Reactor.ext
    simp [ports, roles, acts, state, prios] at h
    simp only [h]
    obtain ⟨_, _, _, _, h₁, h₂, _⟩ := h
    simp [rcns_ext h₁, nest_ext h₂]

@[ext]
theorem ext {rtr₁ rtr₂ : Reactor ι υ} : 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.roles = rtr₂.roles ∧
  rtr₁.acts = rtr₂.acts   ∧ rtr₁.state = rtr₂.state ∧ 
  rtr₁.rcns  = rtr₂.rcns  ∧ rtr₁.nest  = rtr₂.nest  ∧ 
  rtr₁.prios = rtr₂.prios → rtr₁ = rtr₂ :=
  λ h => ext_iff.mpr h

end Reactor