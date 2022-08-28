import ReactorModel.Components.Reactor.Raw

open Classical

namespace Raw.Reactor

protected structure WellFormed.Direct (rtr : Raw.Reactor) : Prop where
  nestFinite :   { i | rtr.nest i ≠ none }.finite
  uniqueIDs :    (l₁ l₂ : Raw.Lineage rtr i) → l₁ = l₂ 
  orderability : (Raw.Orderable rtr rcn₁ rcn₂) → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)   
  uniqueInputs : (rtr.nest iₙ = some n) → (iₚ ∈ (n.ports' .in).ids) → (rtr.rcns i₁ = some rcn₁) → (rtr.rcns i₂ = some rcn₂) → (i₁ ≠ i₂) → (iₚ ∈ rcn₁.deps .out) → iₚ ∉ rcn₂.deps .out
  normDeps :     (n ∈ rtr.norms.values) → ↑(n.deps k) ⊆ (↑rtr.acts.ids ∪ ↑(rtr.ports' k).ids ∪ (rtr.nestedPortIDs k.opposite))
  mutDeps :      (m ∈ rtr.muts.values) → (m.deps .in ⊆ rtr.acts.ids ∪ (rtr.ports' .in).ids) ∧ ↑(m.deps .out) ⊆ ↑rtr.acts.ids ∪ ↑(rtr.ports' .out).ids ∪ (rtr.nestedPortIDs .in)

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

def ports : Reactor → ID ⇉ Port             := (·.raw.ports)
def acts  : Reactor → ID ⇉ Time.Tag ⇉ Value := (·.raw.acts)
def state : Reactor → ID ⇉ Value            := (·.raw.state)
def rcns  : Reactor → ID ⇉ Reaction         := (·.raw.rcns)

def nest (rtr : Reactor) : ID ⇉ Reactor :=
  let raw : ID ⇉ Raw.Reactor := { lookup := rtr.raw.nest, finite := rtr.rawWF.direct.nestFinite }
  raw.attach.map (λ ⟨_, h⟩ => Reactor.fromRaw _ (by
      have ⟨_, hm⟩ := Finmap.values_def.mp h
      exact rtr.rawWF.ancestor (Raw.Reactor.Ancestor.nest hm)
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

theorem nest_ind 
  {motive : Reactor → Prop}  
  (base : ∀ rtr, (rtr.nest = ∅) → motive rtr)
  (step : ∀ rtr, (∀ n ∈ rtr.nest.values, motive n) → motive rtr) :
  (∀ rtr, motive rtr) := by
  sorry

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
    let f := rtr.nest.values.bUnion (λ n => (n.ports' k).ids)
    suffices h : description ⊆ ↑f from Set.finite.subset (Finset.finite_to_set _) h
    simp [Set.subset_def]
  finite.toFinset

private theorem mem_raw_nestedPortIDs_to_mem_nestedPortIDs {rtr : Reactor} :
  (i ∈ rtr.raw.nestedPortIDs k) → (i ∈ rtr.nestedPortIDs k) := by
  simp [nestedPortIDs, Raw.Reactor.nestedPortIDs, Set.finite.mem_to_finset]
  intro j r hn hi
  have rwf := rtr.rawWF.ancestor (.nest hn)
  let rtr' := Reactor.fromRaw r rwf
  have hr : r = rtr'.raw := rfl
  rw [hr] at hn
  exists rtr'
  simp [Finmap.values_def.mpr ⟨_, nest_mem_raw_iff.mpr hn⟩, ports']
  simp [Raw.Reactor.ports'] at hi
  exact hi

noncomputable def scheduledTags (σ : Reactor) : Finset Time.Tag := 
  σ.acts.values.bUnion (·.ids)

inductive Orderable (rtr : Reactor) (rcn₁ rcn₂ : Reaction) : Prop
  | impure : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (¬rcn₁.isPure) → (¬rcn₂.isPure)            → Orderable rtr rcn₁ rcn₂
  | output : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.deps .out ∩ rcn₂.deps .out).nonempty → Orderable rtr rcn₁ rcn₂
  | muts   : (rtr.rcns i₁ = rcn₁) → (rtr.rcns i₂ = rcn₂) → (i₁ ≠ i₂) → (rcn₁.isMut) → (rcn₂.isMut)                → Orderable rtr rcn₁ rcn₂

theorem orderability {rtr : Reactor} : (Orderable rtr rcn₁ rcn₂) → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  | .impure h₁ h₂ hi hp₁ hp₂ => rtr.rawWF.direct.orderability (.impure h₁ h₂ hi hp₁ hp₂)
  | .output h₁ h₂ hi ho => rtr.rawWF.direct.orderability (.output h₁ h₂ hi ho)
  | .muts h₁ h₂ hi hm₁ hm₂ => rtr.rawWF.direct.orderability (.muts h₁ h₂ hi hm₁ hm₂)

theorem uniqueInputs {rtr : Reactor} :
  (rtr.nest iₙ = some n) → (iₚ ∈ (n.ports' .in).ids) → 
  (rtr.rcns i₁ = some rcn₁) → (rtr.rcns i₂ = some rcn₂) → (i₁ ≠ i₂) → 
  (iₚ ∈ rcn₁.deps .out) → iₚ ∉ rcn₂.deps .out :=
  λ hn hp hr₁ hr₂ hi ho => rtr.rawWF.direct.uniqueInputs (nest_mem_raw_iff.mp hn) hp hr₁ hr₂ hi ho
  
theorem normDeps {rtr : Reactor} :
  (n ∈ rtr.norms.values) → (n.deps k) ⊆ (rtr.acts.ids ∪ (rtr.ports' k).ids ∪ (rtr.nestedPortIDs k.opposite)) := by
  intro hn
  simp [Finset.subset_iff, Finset.mem_union]
  intro i hi
  have hs : ↑(n.deps k) ⊆ (↑rtr.raw.acts.ids ∪ ↑(rtr.raw.ports' k).ids ∪ (rtr.raw.nestedPortIDs k.opposite)) := rtr.rawWF.direct.normDeps hn
  simp [Set.subset_def, Set.mem_union] at hs
  specialize hs i hi
  cases hs
  case inl hc => exact .inl hc
  case inr hc => exact .inr (mem_raw_nestedPortIDs_to_mem_nestedPortIDs hc)

theorem mutDeps {rtr : Reactor} :
  (m ∈ rtr.muts.values) → 
  (m.deps .in ⊆ rtr.acts.ids ∪ (rtr.ports' .in).ids) ∧ 
  (m.deps .out) ⊆ rtr.acts.ids ∪ (rtr.ports' .out).ids ∪ (rtr.nestedPortIDs .in) := by
  intro hm
  have ⟨hi, ho⟩ := rtr.rawWF.direct.mutDeps hm
  simp [Finset.subset_iff, Finset.mem_union, Set.subset_def, Set.mem_union] at *
  refine ⟨?ins, ?outs⟩ <;> intro _ hj  
  case ins => exact hi hj
  case outs =>
    cases ho _ hj
    case inl hc => exact .inl hc
    case inr hc => exact .inr (mem_raw_nestedPortIDs_to_mem_nestedPortIDs hc)

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

private def Lineage.toRaw : (Lineage σ cmp i) → Raw.Lineage σ.raw i
  | .end (.prt) h => .prt h
  | .end (.act) h => .act h
  | .end (.stv) h => .stv h
  | .end (.rcn) h => .rcn h
  | .end (.rtr) h => .rtr (σ.nest_raw_eq_raw_nest.eqIDs i |>.mp h)
  | .nest l hn => .nest l.toRaw (nest_mem_raw_iff.mp hn)

theorem uniqueIDs (l₁ l₂ : Lineage σ cmp i) : l₁ = l₂ := by
  have h := σ.rawWF.direct.uniqueIDs l₁.toRaw l₂.toRaw
  induction l₁ <;> cases l₂ <;> simp [Lineage.toRaw] at *
  case nest.nest hi _ _ _ _ =>
    have hr := Reactor.raw_ext_iff.mpr h.left
    subst hr
    simp [h.right.left, hi _ $ eq_of_heq h.right.right]
  case' end.nest cmp _ _ _ _ _, nest.end cmp _ _ _ _ =>
    cases cmp <;> simp [Lineage.toRaw] at h
    
end Reactor