import ReactorModel.Components.Reactor.Raw

open Port Classical

namespace Raw.Reactor

protected structure WellFormed.Direct (rtr : Raw.Reactor) : Prop where
  nestFinite : { i | rtr.nest i ≠ none }.finite
  uniqueIDs :  ∀ l₁ l₂ : Lineage rtr i, l₁ = l₂ 
  uniqueIns :  ∀ {iₚ p iₙ n i₁ rcn₁ i₂ rcn₂}, (rtr.nest iₙ = some n) → (n.ports' .in iₚ = some p) → (rtr.rcns i₁ = some rcn₁) → (rtr.rcns i₂ = some rcn₂) → (i₁ ≠ i₂) → (iₚ ∈ rcn₁.deps .out) → iₚ ∉ rcn₂.deps .out
  normDeps :   ∀ {n k}, (n ∈ rtr.norms.values) → ↑(n.deps k) ⊆ (↑rtr.acts.ids ∪ ↑(rtr.ports' k).ids ∪ (rtr.nestedPortIDs k.opposite))
  mutDeps :    ∀ {m}, (m ∈ rtr.muts.values) → (m.deps .in ⊆ rtr.acts.ids ∪ (rtr.ports' .in).ids) ∧ ↑(m.deps .out) ⊆ ↑rtr.acts.ids ∪ ↑(rtr.ports' .out).ids ∪ (rtr.nestedPortIDs .in)
  rcnsTotal :  ∀ {rcn₁ rcn₂}, rtr.rcnsNeedTotalOrder rcn₁ rcn₂ → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)   

-- To define properties of reactors recursively, we need a concept of containment.
-- Containment in a reactor can come in two flavors: 
--
-- 1. `nested`: `r₁` contains `r₂` directly as nested reactor
-- 2. `creatable`: there exists a reaction (which must be a mutation) in `r₁` which
--    can produce a `Raw.Change.create` which contains `r₂`
--
-- The `Ancestor` relation forms the transitive closure over the previous cases.
inductive Ancestor : Raw.Reactor → Raw.Reactor → Prop 
  | nest : (parent.nest i = some child) → Ancestor parent child
  | trans : (Ancestor rtr₁ rtr₂) → (Ancestor rtr₂ rtr₃) → (Ancestor rtr₁ rtr₃)

-- This property ensures "properness" of a reactor in two steps:
-- 
-- 1. `direct` ensures that the given reactor satisfies all constraints
--    required for a "proper" reactor.
-- 2. `offspring` ensures that all nested and creatable reactors also satisfy `directlyWellFormed`.
--    The `isAncestorOf` relation formalizes the notion of (transitive) nesting and "creatability".
structure WellFormed (σ : Raw.Reactor) : Prop where
  direct : WellFormed.Direct σ 
  offspring : ∀ {rtr}, Ancestor σ rtr → WellFormed.Direct rtr

theorem WellFormed.ancestor {rtr₁ rtr₂ : Raw.Reactor} (hw : WellFormed rtr₁)  (ha : Ancestor rtr₁ rtr₂) : WellFormed rtr₂ := {
  direct := hw.offspring ha,
  offspring := (hw.offspring $ ha.trans ·)
}

end Raw.Reactor

-- A `Reactor` is a raw reactor that is also well-formed.
--
-- Side note: 
-- The `fromRaw ::` names the constructor of `Reactor`.
structure Reactor where
  private fromRaw ::
    private raw : Raw.Reactor
    private rawWF : Raw.Reactor.WellFormed raw  

namespace Reactor

def ports (rtr : Reactor) : ID ⇉ Port              := rtr.raw.ports
def acts  (rtr : Reactor) : ID ⇉ Time.Tag ⇉ Value  := rtr.raw.acts
def state (rtr : Reactor) : ID ⇉ Value             := rtr.raw.state
def rcns  (rtr : Reactor) : ID ⇉ Reaction          := rtr.raw.rcns

def nest (rtr : Reactor) : ID ⇉ Reactor :=
  let raw : ID ⇉ Raw.Reactor := { lookup := rtr.raw.nest, finite := rtr.rawWF.direct.nestFinite }
  raw.attach.map (λ ⟨_, h⟩ => Reactor.fromRaw _ (by
      have ⟨_, hm⟩ := Finmap.values_def.mp h
      exact rtr.rawWF.ancestor $ Raw.Reactor.Ancestor.nest hm
    )
  )  

-- A raw-based extensionality theorem for `Reactor`.
-- We also define a proper extensionality theorem called `ext_iff`.
private theorem raw_ext_iff {rtr₁ rtr₂ : Reactor} : rtr₁ = rtr₂ ↔ rtr₁.raw = rtr₂.raw := by
  constructor <;> (
    intro h
    cases rtr₁
    cases rtr₂
    simp at h
    simp [h]
  )

theorem nest_raw_eq_raw_nest (rtr : Reactor) : Finmap.forall₂' (·.raw = ·) rtr.nest rtr.raw.nest := {
  eqIDs := by
    intro i
    simp only [Reactor.nest, Finmap.map_mem_ids, Finmap.attach_mem_ids]
    exact Finmap.ids_def,
  rel := by
    intro _ _ _ hr hr'
    simp only [nest] at hr
    have ⟨⟨m, hm⟩, ⟨h₁, h₂⟩⟩ := Finmap.map_def hr
    simp [←h₂, Option.some_inj.mp $ (Finmap.attach_def h₁).symm.trans hr']
}

theorem nest_mem_raw_iff {rtr rtr' : Reactor} {i} : rtr.nest i = rtr' ↔ rtr.raw.nest i = rtr'.raw := by
  constructor
  case mp =>
    intro h
    have ⟨hi, hv⟩ := nest_raw_eq_raw_nest rtr
    have hm : i ∈ rtr.nest.ids := Finmap.ids_def'.mpr ⟨rtr', h⟩
    have ⟨_, hx⟩ := Option.ne_none_iff_exists.mp $ (hi i).mp hm
    have he := hv h hx.symm
    simp [←hx, he]
  case mpr =>
    intro h
    have ⟨hi, hv⟩ := nest_raw_eq_raw_nest rtr
    have hi := (hi i).mpr (Option.ne_none_iff_exists.mpr ⟨rtr'.raw, h.symm⟩)
    have ⟨x, hx⟩ := Finmap.ids_def'.mp hi
    have he := hv hx h
    simp [hx]
    exact raw_ext_iff.mpr he  

theorem ext_iff {rtr₁ rtr₂ : Reactor} : 
  rtr₁ = rtr₂ ↔ 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts  ∧ 
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns = rtr₂.rcns ∧ 
  rtr₁.nest  = rtr₂.nest := by
  constructor
  case mp =>
    intro h
    simp [ports, acts, state, raw_ext_iff.mp h]
    constructor <;> simp only [Finmap.ext, h]
  case mpr =>
    intro h
    apply raw_ext_iff.mpr
    apply Raw.Reactor.ext_iff.mpr
    simp only [ports, rcns, acts, state] at h
    simp [h]
    have ⟨_, _, _, _, h⟩ := h
    funext i
    have h₁ :=  nest_raw_eq_raw_nest rtr₁
    have h₁₁ := nest_raw_eq_raw_nest rtr₁
    have h₂ :=  nest_raw_eq_raw_nest rtr₂
    have h₂₂ := nest_raw_eq_raw_nest rtr₂
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
      have hr₁ := h₁₁.rel hx hc
      have hr₂ := h₂.rel hx hy.symm
      simp [←hr₁, ←hr₂]
    
@[ext]
theorem ext {rtr₁ rtr₂ : Reactor} : 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts  ∧ 
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns  = rtr₂.rcns ∧ 
  rtr₁.nest  = rtr₂.nest → 
  rtr₁ = rtr₂ :=
  λ h => ext_iff.mpr h

noncomputable def ports' (rtr : Reactor) (k : Kind) : ID ⇉ Port :=
  rtr.ports.filter' (·.kind = k)

noncomputable def norms (rtr : Reactor) : ID ⇉ Reaction :=
  rtr.rcns.filter' (·.isNorm)

theorem mem_muts_isNorm {rtr: Reactor} : (rtr.norms i = some n) → n.isNorm :=
  λ h => Finmap.filter'_mem.mp h |>.right

noncomputable def muts (rtr : Reactor) : ID ⇉ Reaction :=
  rtr.rcns.filter' (·.isMut)  

theorem mem_muts_isMut {rtr: Reactor} : (rtr.muts i = some m) → m.isMut :=
  λ h => Finmap.filter'_mem.mp h |>.right

noncomputable def nestedPortIDs (rtr : Reactor) (k : Kind) : Finset ID :=
  let description := { i | ∃ n, n ∈ rtr.nest.values ∧ i ∈ (n.ports' k).ids }
  let finite : description.finite := by
    let f : Finset ID := rtr.nest.values.bUnion (λ n => (n.ports' k).ids)
    suffices h : description ⊆ ↑f from Set.finite.subset (Finset.finite_to_set _) h
    simp [Set.subset_def]
  finite.toFinset

noncomputable def scheduledTags (σ : Reactor) : Finset Time.Tag := 
  σ.acts.values.bUnion (·.ids)

/-
-- TODO (maybe): Factor out the overlap between the proofs of `wfNormDeps` and `wfMutDeps`.

-- This constraint constrains the anti/-dependencies of `rtr`'s normal reactions, such that:
-- 1. their dependencies can only be input ports of `rtr` or output ports of reactors
--    nested directly in `rtr`
-- 2. their antidependencies can only be output ports of `rtr` or input ports of reactors
--    nested directly in `rtr`
theorem wfNormDeps {rtr : Reactor} {n : Reaction} (r : Port.Role) (h : n ∈ rtr.norms.values) : 
  n.deps r ⊆ rtr.acts.ids ∪ (rtr.ports' r).ids ∪ rtr.nestedPortIDs r.opposite := by
  simp only [Finset.subset_iff, Finset.mem_union]
  intro j hj
  simp only [norms, Finmap.filter'_mem_values] at h
  have ⟨i, h, hn⟩ := h
  have ⟨nr, hr⟩ := rcns_has_raw h
  have he := RawEquiv.rcns rtr
  have hnr := (Reaction.RawEquiv.isNorm_iff $ he.rel h hr).mp hn
  have hw := rtr.rawWF.direct.wfNormDeps nr i r hr
  simp [Set.subset_def, Set.mem_union] at hw
  rw [(he.rel h hr).deps] at hj
  cases (hw hnr j hj)
  case inl hw => exact Or.inl hw
  case inr hw =>
    apply Or.inr
    have ⟨i', ri', h₁, h₂⟩ := hw
    simp [nestedPortIDs, Set.finite.mem_to_finset]
    have hrip := Raw.Reactor.Ancestor.preserves_wf (Raw.Reactor.Ancestor.nested h₁) rtr.rawWF
    let rip := Reactor.fromRaw ri' hrip
    exists rip
    constructor
    case h.left =>
      simp [Finmap.values_def]
      exists i'
      exact nest_mem_raw_iff.mpr h₁
    case h.right =>
      simp [ports', Raw.Reactor.ports', ports] at h₂ ⊢
      exact h₂

-- This constraint constrains the anti/-dependencies of `rtr`'s mutations, such that:
-- 1. their dependencies can only be input ports of `rtr`
-- 2. their antidependencies can only be output ports of `rtr` or input ports of reactors
--    nested directly in `rtr`
theorem wfMutDeps {rtr : Reactor} {m : Reaction} (r : Port.Role) (h : m ∈ rtr.muts.values) : 
  (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (m.deps Role.out ⊆ (rtr.ports' Role.out).ids ∪ rtr.nestedPortIDs Role.in) := by
  simp only [muts, Finmap.filter'_mem_values] at h
  have ⟨i, h, hm⟩ := h
  have ⟨mr, hr⟩ := rcns_has_raw h
  have he := RawEquiv.rcns rtr
  have hq := he.rel h hr
  have hrm := (Reaction.RawEquiv.isMut_iff hq).mp hm
  have hw := rtr.rawWF.direct.wfMutDeps mr i hr hrm
  have ⟨h₁, h₂⟩ := hw
  clear hw
  constructor
  case left =>
    rw [hq.deps]
    simp [ports', ports, Raw.Reactor.ports'] at h₁ ⊢
    exact h₁
  case right =>
    clear h₁
    simp [Set.subset_def, Set.mem_union] at h₂
    simp [Finset.subset_iff]  
    rw [hq.deps]
    intro j hj
    cases (h₂ j hj)
    case inl h => exact Or.inl h
    case inr h =>
      apply Or.inr
      have ⟨i', ri', h₁, h₂⟩ := h
      simp [nestedPortIDs, Set.finite.mem_to_finset]
      have hrip := Raw.Reactor.Ancestor.preserves_wf (Raw.Reactor.Ancestor.nested h₁) rtr.rawWF
      let rip := Reactor.fromRaw ri' hrip
      exists rip
      constructor
      case h.left =>
        simp [Finmap.values_def]
        exists i'
        exact nest_mem_raw_iff.mpr h₁
      case h.right =>
        simp [ports', Raw.Reactor.ports', ports] at h₂ ⊢
        exact h₂
-/
-/
-/

inductive rcnsNeedTotalOrder (rtr : Reactor) (rcn₁ rcn₂ : Reaction) 
  | impure {i₁ i₂} : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (¬rcn₁.isPure) → (¬rcn₂.isPure) → rcnsNeedTotalOrder rtr rcn₁ rcn₂
  | output {i₁ i₂} : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.deps .out ∩ rcn₂.deps .out ≠ ∅) → rcnsNeedTotalOrder rtr rcn₁ rcn₂
  | muts   {i₁ i₂} : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.isMut) → (rcn₂.isMut) → rcnsNeedTotalOrder rtr rcn₁ rcn₂

theorem rcnsTotalOrder {rtr : Reactor} {rcn₁ rcn₂ : Reaction} :
  (rtr.rcnsNeedTotalOrder rcn₁ rcn₂) → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio) := by
  sorry

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Cmp
  | rtr -- Nested reactors
  | rcn -- Reactions
  | prt -- Ports
  | act -- Actions
  | stv -- State variables

-- The *type* corresponding to the component labeled by a given `Cmp`.
-- 
-- Note that the types for `prt` and `stv` are just `υ`, because IDs don't refer to
-- the entire entire mappinngs, but rather the single values within them.
abbrev Cmp.type : Cmp → Type _
  | .rtr => Reactor
  | .rcn => Reaction
  | .prt => Port
  | .act => Time.Tag ⇉ Value
  | .stv => Value

-- Associates each type of component with the finmap in which it can be found inside
-- of a reactor. We use this in `Object` to generically resolve the lookup for *some*
-- component and *some* ID.
abbrev cmp? : (cmp : Cmp) → Reactor → ID ⇉ cmp.type
  | .rtr => Reactor.nest
  | .rcn => Reactor.rcns
  | .prt => Reactor.ports
  | .act => Reactor.acts
  | .stv => Reactor.state

-- A `Lineage` for a given ID `i` in the context of a reactor `σ` is a 
-- structure that traces a path through the nested reactors of `σ` that lead
-- to the component identified by `i`.
-- 
-- A `Lineage` captures two important aspects:
-- 
-- 1. The non-recursive constructors (`rtr`, `rcn`, `prt` and `stv`) tell us
-- what kind of component is identified by `i`.
-- 2. The recursive `nest` constructor captures all of the reactors `σ'` that
-- need to be traversed from the root reactor `σ` to arrive at the immediate
-- parent of `i`.
--
-- We use this structure to define ID-uniqueness (`uniqueIDs`) in reactors as
-- well as hierarchy accessors in Components>Reactor>Hierarchy.lean.
inductive Lineage : Reactor → Cmp → ID → Type _
  | «end» cmp : (i ∈ (σ.cmp? cmp).ids) → Lineage σ cmp i
  | nest {cmp} : (Lineage rtr cmp i) → (σ.nest j = some rtr) → Lineage σ cmp i

private def Lineage.toRaw : (Lineage σ cmp i) → Raw.Reactor.Lineage σ.raw i
  | .end (.prt) h => .prt h
  | .end (.act) h => .act h
  | .end (.stv) h => .stv h
  | .end (.rcn) h => .rcn h
  | .end (.rtr) h => .rtr (σ.nest_raw_eq_raw_nest.eqIDs i |>.mp h)
  | .nest l hn => .nest l.toRaw (nest_mem_raw_iff.mp hn)

theorem uniqueIDs (l₁ l₂ : Lineage σ cmp i) : l₁ = l₂ := by
  sorry

-- Any component in a reactor that is addressable by an ID has a unique ID.
-- We define this property in terms of `Lineage`s, since a components is
-- addressable by an ID in a reactor iff it has a lineage in that reactor
-- (by construction of `Lineage`).
/-theorem uniqueIDs (l₁ l₂ : Lineage σ i) : l₁ = l₂ := by
  have h := σ.rawWF.direct.uniqueIDs l₁.toRaw l₂.toRaw
  induction l₁
  case nest hi =>
    cases l₂ 
    case nest =>
      simp [Lineage.toRaw] at h
      have hr := Reactor.raw_ext_iff.mpr h.left
      subst hr
      simp [h.right.left]
      exact hi _ $ eq_of_heq h.right.right
    case «end» =>
      sorry
    all_goals { contradiction }
  all_goals { cases l₂ <;> (simp_all [Lineage.toRaw]; sorry) }
-/

end Reactor