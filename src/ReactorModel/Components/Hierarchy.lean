import ReactorModel.Components.Reactor.Properties

open Classical 

-- TODO: Redoc
-- TODO: Better notation for cmp.accessor σ, e.g. σ[cmp]

-- Note that `ι` and `υ` live in the same universe:
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Stuck.20at.20solving.20universe.20constraint/near/253232009
variable (ι υ : Type u) [Value υ]

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Cmp
  | rtr -- Nested reactors
  | rcn -- Reactions
  | prt -- Port
  | act -- Actions
  | stv -- State variables

namespace Cmp 

-- The *type* corresponding to the component labeled by a given `Cmp`.
-- 
-- Note that the types for `prt` and `stv` are just `υ`, because IDs don't refer to
-- the entire entire mappinngs, but rather the single values within them.
abbrev type : Cmp → Type _
  | rtr => Reactor ι υ
  | rcn => Reaction ι υ
  | prt => υ
  | act => Time ▸ υ
  | stv => υ

variable {ι υ}

-- Associates each type of component with the finmap in which it can be found inside
-- of a reactor. We use this in `objFor` to generically resolve the lookup for *some*
-- component and *some* ID.
def accessor : (cmp : Cmp) → Reactor ι υ → (ι ▸ cmp.type ι υ)
  | rtr => Reactor.nest
  | rcn => Reactor.rcns
  | prt => Reactor.ports
  | act => Reactor.acts
  | stv => Reactor.state

end Cmp

variable {ι υ}

namespace Reactor

-- TODO: Docs
--       Mention that we do the whole Option ι so that ⊤ can never appear inside a reactor.
--       Its more like a label.
notation "⊤" => Option.none

namespace Lineage

-- The "direct parent" in a lineage is the reactor which contains the target of the lineage.
-- This function returns that reactor along with its ID.
-- If the direct parent is the top-level reactor `σ`, then the ID is `⊤`.
def directParent {σ : Reactor ι υ} {i} : Lineage σ i → (Option ι × Reactor ι υ)
  | rtr _ => (⊤, σ)
  | rcn _ => (⊤, σ)
  | prt _ => (⊤, σ)
  | act _ => (⊤, σ)
  | stv _ => (⊤, σ)
  | nest σ' i' (rtr _) _ => (i', σ')
  | nest σ' i' (rcn _) _ => (i', σ')
  | nest σ' i' (prt _) _ => (i', σ')
  | nest σ' i' (stv _) _ => (i', σ')
  | nest _  _  l       _ => directParent l -- By case distinction `l` is a `Lineage.nest`.

def target {σ : Reactor ι υ} {i} : Lineage σ i → Cmp 
  | rtr _ => Cmp.rtr
  | rcn _ => Cmp.rcn
  | prt _ => Cmp.prt
  | act _ => Cmp.act
  | stv _ => Cmp.stv
  | nest _ _ l _ => target l

def fromCmp (σ : Reactor ι υ) (i) : (cmp : Cmp) → (h : i ∈ (cmp.accessor σ).ids) → Lineage σ i
  | Cmp.rtr, h => Lineage.rtr h
  | Cmp.rcn, h => Lineage.rcn h
  | Cmp.prt, h => Lineage.prt h
  | Cmp.act, h => Lineage.act h
  | Cmp.stv, h => Lineage.stv h

def retarget {σ : Reactor ι υ} {i} : (l : Lineage σ i) → (cmp : Cmp) → i ∈ (cmp.accessor l.directParent.snd).ids → Lineage σ i
  | nest σ' i' l' h', cmp, h => Lineage.nest σ' i' (retarget l' cmp h) h'
  | _, cmp, h => Lineage.fromCmp σ i cmp h

set_option maxHeartbeats 100000 in
theorem retarget_target (σ : Reactor ι υ) (i) (l : Lineage σ i) (cmp h) :
  (l.retarget cmp h).target = cmp := by
  induction l 
  case nest σ σ' i i' l' hσ' hi =>  
    have hp : l'.directParent.snd = (nest σ' i' l' hσ').directParent.snd := 
      by cases l' <;> simp only [directParent]
    rw [←hp] at h
    simp only [←(hi h)]
    cases cmp <;> (simp only [target]; rfl)
  all_goals { cases cmp <;> simp only [target, retarget] }

theorem retarget_ne {σ : Reactor ι υ} {i} (l : Lineage σ i) {cmp} (h) :
  cmp ≠ l.target → l ≠ l.retarget cmp h := by 
  intro hn hc
  have h' := Lineage.retarget_target σ i l cmp h
  rw [←hc] at h'
  have := Eq.symm h'
  contradiction

end Lineage

-- The `containerOf` relation is used to determine whether a given ID `c`
-- identifies a reactor that contains a given object identified by ID `i`.
-- In other words, whether `c` identifies the parent of `i`.
-- The *kind* of component addressed by `i` is not required, as all IDs in
-- a reactor are unique (by `Reactor.uniqueIDs`).
--
-- Formalization:
-- We use the concept of lineages to "find" the path of reactor-IDs that leads
-- us through `σ` to `i`. If such a lineage exists we check whether `c` is the ID
-- of the last reactor in that path, because by construction (of lineages) *that* 
-- is the reactor that contains `i`.
-- Note that while `c` *can* be the top-level ID `⊤`, `i` can't.
-- We need to restrict `i` in this way, because `Lineage`s are only defined over
-- non-optional IDs. In practice, this isn't really a restriction though, because
-- we could easily extend the definition of `containerOf` to check whether `i = ⊤`
-- and yield `False` in that case (as the top-level reactor will never have a
-- parent container).
def containerOf (σ : Reactor ι υ) (i : ι) (c : Option ι) : Prop := 
  ∃ l : Lineage σ i, (l.directParent).fst = c 

-- This notation is chosen to be akin to the address notation in C.
notation σ:max " &[" i "]= " c:max => Reactor.containerOf σ i c

-- In the `containerOf` relation, any given ID can have at most one parent (`containerOf` is functional).
theorem containerOf_unique {σ : Reactor ι υ} {i : ι} {c₁ c₂ : Option ι} :
  σ &[i]= c₁ → σ &[i]= c₂ → c₁ = c₂ := by
  intro h₁ h₂
  obtain ⟨l₁, h₁⟩ := h₁
  obtain ⟨l₂, h₂⟩ := h₂
  simp [←h₁, ←h₂, σ.uniqueIDs l₁ l₂]

-- The `objFor` relation is used to determine whether a given ID `i` identifies
-- an object `o` of component type `cmp`.
--
-- Example: 
-- If `σ.objFor Cmp.rcn i x`, then:
-- * `σ` is the "context" (top-level) reactor.
-- * `i` is interpreted as being an ID that refers to a reaction (because of `Cmp.rcn`).
-- * `x` is the `Reaction` identified by `i`.
--
-- Formalization:
-- We use the concept of lineages to "find" the path of reactor-IDs that leads
-- us through `σ` to `i`. If such a lineage exists we obtain the last reactor in
-- that path (`l.directParent.snd`). From that reactor we try to obtain an object 
-- identified by `i` of component kind `cmp` (cf. `Cmp.accessor`).
-- We then check whether the given object `o` matches that object.
--
-- Technicalities:
-- The left side of the equality produces an optional value, as it is possible
-- that no value of component kind `cmp` is found for ID `i`.
-- Thus the right side is automatically lifted by Lean to `some o`. 
-- It *would* be possible to avoid this optionality, as a lineage for `i` always
-- contains a proof that `i` identifies an object in its parent reactor.
-- In this case the kind of lineage and given `cmp` would have to be matched, e.g. 
-- by adding an instance of `Cmp` into the type of `Lineage`.
-- This leads to heterogeneous equality though, and is therefore undesirable:
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20Exfalso.20HEq
def objFor (σ : Reactor ι υ) (cmp : Cmp) (i : ι) (o : cmp.type ι υ) : Prop := 
  ∃ l : Lineage σ i, (cmp.accessor l.directParent.snd) i = o

-- This notation is chosen to be akin to the dereference notation in C.
notation σ:max " *[" cmp ", " i "]= " o:max => Reactor.objFor σ cmp i o

-- In the `objFor` relation, any given ID can have associated objects of at most one component type.
-- E.g. an ID cannot have associated objects of type `Cmp.rcn` *and* `Cmp.prt`.
-- Cf. `objFor_unique_obj` for further information.
theorem objFor_unique_cmp {σ : Reactor ι υ} {i : ι} {cmp₁ cmp₂ : Cmp} {o₁ : cmp₁.type ι υ} {o₂ : cmp₂.type ι υ} :
  (σ *[cmp₁, i]= o₁) → (σ *[cmp₂, i]= o₂) → cmp₁ = cmp₂ := by
  intro h₁ h₂
  obtain ⟨l₁, h₁⟩ := h₁
  obtain ⟨l₂, h₂⟩ := h₂
  have hu := σ.uniqueIDs l₁ l₂
  rw [←hu] at h₂
  by_contra hc
  have h₁ := Option.ne_none_iff_exists.mpr ⟨o₁, Eq.symm h₁⟩ |> Finmap.ids_def.mpr
  have h₂ := Option.ne_none_iff_exists.mpr ⟨o₂, Eq.symm h₂⟩ |> Finmap.ids_def.mpr
  by_cases hc₁ : cmp₁ = l₁.target
  case neg =>
    have := Lineage.retarget_ne l₁ h₁ hc₁
    have := σ.uniqueIDs l₁ $ l₁.retarget cmp₁ h₁
    contradiction
  case pos =>
    by_cases hc₂ : cmp₂ = l₂.target
    case neg =>
      have := Lineage.retarget_ne l₂ h₂ hc₂
      have := σ.uniqueIDs l₂ $ l₂.retarget cmp₂ h₂
      contradiction
    case pos =>
      rw [hu] at hc₁
      rw [←hc₂] at hc₁
      contradiction

-- In the `objFor` relation, any given ID can have at most one associated object. 
--
-- Technicalities:
-- There are really two aspects of uniqueness that come together in `objFor`.
--
-- 1. Any given ID can have associated objects of at most one component type, as shown by `objFor_unique_cmp`.
-- 2. Any given ID can have a most one associated object of each component type, as shown here.
--
-- The result is that each ID can have at most one associated object, even across component types.
-- We do not show this together as this would involve using `HEq`.
-- If this is important though, the two theorems can be used in succession:
-- First, `objFor_unique_obj` can be used to establish equality of the component types.
-- After appropriate type casting (using the previous result), `objFor_unique_obj` can be used to show
-- object equality. 
theorem objFor_unique_obj {σ : Reactor ι υ} {i : ι} {cmp : Cmp} {o₁ o₂ : cmp.type ι υ} : 
  (σ *[cmp, i]= o₁) → (σ *[cmp, i]= o₂) → o₁ = o₂ := by
  intro h₁ h₂
  obtain ⟨l₁, h₁⟩ := h₁
  obtain ⟨l₂, h₂⟩ := h₂
  have hu := σ.uniqueIDs l₁ l₂
  rw [hu] at h₁
  simp [h₁] at h₂
  exact h₂

inductive update (cmp : Cmp) (v : cmp.type ι υ) : ι → Reactor ι υ → Reactor ι υ → Prop :=
  | top {i σ₁ σ₂} : 
    (∀ cmp' i', (cmp' ≠ cmp ∨ i' ≠ i) → cmp'.accessor σ₁ i' = cmp'.accessor σ₂ i') → 
    (σ₁.prios = σ₂.prios) → 
    (σ₁.roles = σ₂.roles) → 
    (cmp.accessor σ₂ i = v) → 
    update cmp v i σ₁ σ₂
  | nested {i σ₁ σ₂} {j rtr₁ rtr₂} :
    (∀ cmp', cmp' ≠ Cmp.rtr → cmp'.accessor σ₁ = cmp'.accessor σ₂) → 
    (σ₁.prios = σ₂.prios) → 
    (σ₁.roles = σ₂.roles) → 
    (σ₁.nest j = some rtr₁) →
    (σ₂.nest j = some rtr₂) →
    (∀ j', j' ≠ j → σ₁.nest j' = σ₂.nest j') →
    (update cmp v i rtr₁ rtr₂) →
    update cmp v i σ₁ σ₂

notation σ₁:max " -[" cmp ", " i " := " v "]→ " σ₂:max => Reactor.update cmp v i σ₁ σ₂

-- TODO: Find out how to solve some of the auxiliary proofs more concisely.

private theorem update_unique_aux₁ {σ₁ σ₂ σ₃ : Reactor ι υ} {cmp₁ cmp₂ : Cmp} {i : ι}
  (h₁ : ∀ cmp' i', (cmp' ≠ cmp₁ ∨ i' ≠ i) → cmp'.accessor σ₁ i' = cmp'.accessor σ₂ i')
  (h₂ : ∀ cmp' i', (cmp' ≠ cmp₁ ∨ i' ≠ i) → cmp'.accessor σ₁ i' = cmp'.accessor σ₃ i') 
  (hn : cmp₂ ≠ cmp₁) :
  cmp₂.accessor σ₂ = cmp₂.accessor σ₃ := by
  have h₁' : ∀ j, (cmp₂.accessor σ₁) j = (cmp₂.accessor σ₂) j := by intro j; exact h₁ cmp₂ j (Or.inl hn)  
  have h₂' : ∀ j, (cmp₂.accessor σ₁) j = (cmp₂.accessor σ₃) j := by intro j; exact h₂ cmp₂ j (Or.inl hn)
  have hf₁ := Finmap.ext_iff.mpr h₁'
  have hf₂ := Finmap.ext_iff.mpr h₂'
  simp only [hf₁] at hf₂
  exact hf₂

private theorem update_unique_aux₂ {σ₁ σ₂ σ₃ : Reactor ι υ} {cmp : Cmp} {i : ι} {v : cmp.type ι υ}
  (h₁ : ∀ cmp' j, (cmp' ≠ cmp ∨ j ≠ i) → cmp'.accessor σ₁ j = cmp'.accessor σ₂ j)
  (h₂ : ∀ cmp' j, (cmp' ≠ cmp ∨ j ≠ i) → cmp'.accessor σ₁ j = cmp'.accessor σ₃ j)
  (hi₁ : cmp.accessor σ₂ i = some v)
  (hi₂ : cmp.accessor σ₃ i = some v) :
  cmp.accessor σ₂ = cmp.accessor σ₃ := by
  apply Finmap.ext
  intro j
  by_cases hc : j = i
  case pos => simp only [hc, hi₁, hi₂]
  case neg => simp only [h₁ cmp j (Or.inr hc), Eq.symm $ h₂ cmp j (Or.inr hc)]

private theorem update_unique_aux₃ {σ₁ σ₂ σ₃ : Reactor ι υ} {cmp : Cmp} {i : ι} {v : cmp.type ι υ}
  (h₁ : ∀ cmp' j, (cmp' ≠ cmp ∨ j ≠ i) → cmp'.accessor σ₁ j = cmp'.accessor σ₂ j)
  (h₂ : ∀ cmp' j, (cmp' ≠ cmp ∨ j ≠ i) → cmp'.accessor σ₁ j = cmp'.accessor σ₃ j)
  (hi₁ : cmp.accessor σ₂ i = some v)
  (hi₂ : cmp.accessor σ₃ i = some v) :
  σ₂.ports = σ₃.ports ∧ σ₂.acts = σ₃.acts ∧ σ₂.state = σ₃.state ∧ σ₂.rcns = σ₃.rcns ∧ σ₂.nest = σ₃.nest := by
  cases cmp
  case rtr =>
    have hu₁ := update_unique_aux₂ h₁ h₂ hi₁ hi₂
    have hu₂ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.rcn ≠ Cmp.rtr)
    have hu₃ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.prt ≠ Cmp.rtr)
    have hu₄ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.act ≠ Cmp.rtr)
    have hu₅ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.stv ≠ Cmp.rtr)
    simp only [Cmp.accessor] at hu₁ hu₂ hu₃ hu₄ hu₅
    simp [hu₁, hu₂, hu₃, hu₄, hu₅]
  case rcn =>
    have hu₁ := update_unique_aux₂ h₁ h₂ hi₁ hi₂
    have hu₂ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.rtr ≠ Cmp.rcn)
    have hu₃ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.prt ≠ Cmp.rcn)
    have hu₄ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.act ≠ Cmp.rcn)
    have hu₅ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.stv ≠ Cmp.rcn)
    simp only [Cmp.accessor] at hu₁ hu₂ hu₃ hu₄ hu₅
    simp [hu₁, hu₂, hu₃, hu₄, hu₅]
  case prt =>
    have hu₁ := update_unique_aux₂ h₁ h₂ hi₁ hi₂
    have hu₂ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.rtr ≠ Cmp.prt)
    have hu₃ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.rcn ≠ Cmp.prt)
    have hu₄ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.act ≠ Cmp.prt)
    have hu₅ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.stv ≠ Cmp.prt)
    simp only [Cmp.accessor] at hu₁ hu₂ hu₃ hu₄ hu₅
    simp [hu₁, hu₂, hu₃, hu₄, hu₅]
  case act =>
    have hu₁ := update_unique_aux₂ h₁ h₂ hi₁ hi₂
    have hu₂ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.rtr ≠ Cmp.act)
    have hu₃ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.rcn ≠ Cmp.act)
    have hu₄ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.prt ≠ Cmp.act)
    have hu₅ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.stv ≠ Cmp.act)
    simp only [Cmp.accessor] at hu₁ hu₂ hu₃ hu₄ hu₅
    simp [hu₁, hu₂, hu₃, hu₄, hu₅]
  case stv =>
    have hu₁ := update_unique_aux₂ h₁ h₂ hi₁ hi₂
    have hu₂ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.rtr ≠ Cmp.stv)
    have hu₃ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.rcn ≠ Cmp.stv)
    have hu₄ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.prt ≠ Cmp.stv)
    have hu₅ := update_unique_aux₁ h₁ h₂ (by intro; contradiction : Cmp.act ≠ Cmp.stv)
    simp only [Cmp.accessor] at hu₁ hu₂ hu₃ hu₄ hu₅
    simp [hu₁, hu₂, hu₃, hu₄, hu₅]

private theorem update_unique_aux₄ {σ₁ σ₂ σ₃ : Reactor ι υ} {cmp : Cmp} 
  (h₁ : ∀ cmp', (cmp' ≠ Cmp.rtr) → cmp'.accessor σ₁ = cmp'.accessor σ₂)
  (h₂ : ∀ cmp', (cmp' ≠ Cmp.rtr) → cmp'.accessor σ₁ = cmp'.accessor σ₃) 
  (hn : cmp ≠ Cmp.rtr) :
  cmp.accessor σ₂ = cmp.accessor σ₃ := by
  have h₁' : cmp.accessor σ₁ = cmp.accessor σ₂ := h₁ cmp hn 
  have h₂' : cmp.accessor σ₁ = cmp.accessor σ₃ := h₂ cmp hn
  simp only [h₁'] at h₂'
  exact h₂'

private theorem update_unique_aux₅ {σ₁ σ₂ σ₃ : Reactor ι υ} 
  (h₁ : ∀ cmp, (cmp ≠ Cmp.rtr) → cmp.accessor σ₁ = cmp.accessor σ₂)
  (h₂ : ∀ cmp, (cmp ≠ Cmp.rtr) → cmp.accessor σ₁ = cmp.accessor σ₃) :
  σ₂.ports = σ₃.ports ∧ σ₂.acts = σ₃.acts ∧ σ₂.state = σ₃.state ∧ σ₂.rcns = σ₃.rcns := by
  have hu₁ := update_unique_aux₄ h₁ h₂ (by intro; contradiction : Cmp.rcn ≠ Cmp.rtr)
  have hu₂ := update_unique_aux₄ h₁ h₂ (by intro; contradiction : Cmp.prt ≠ Cmp.rtr)
  have hu₃ := update_unique_aux₄ h₁ h₂ (by intro; contradiction : Cmp.act ≠ Cmp.rtr)
  have hu₄ := update_unique_aux₄ h₁ h₂ (by intro; contradiction : Cmp.stv ≠ Cmp.rtr)
  simp only [Cmp.accessor] at hu₁ hu₂ hu₃ hu₄
  simp [hu₁, hu₂, hu₃, hu₄]

-- The `update` relation is functional.
theorem update_unique {σ σ₁ σ₂ : Reactor ι υ} {cmp : Cmp} {i : ι} {v : cmp.type ι υ} :
  (σ -[cmp, i := v]→ σ₁) → (σ -[cmp, i := v]→ σ₂) → σ₁ = σ₂ := by
  intro h₁ h₂
  (induction h₁ generalizing σ₂) <;> cases h₂
  case top.top i' σ₁' σ₂' hcn₁ hp₁ hr₁ hi₁ hi₂ hp₂ hr₂ hcn₂ => 
    apply ext
    simp only [hp₁, hr₁] at hp₂ hr₂
    simp only [hp₂, hr₂]
    cases cmp <;> simp only [update_unique_aux₃ hcn₁ hcn₂ hi₁ hi₂]
  case nested.nested i σ₁' σ₂' j rtr₁ rtr₂ hc₁ hp₁ hr₁ hl₁ hl₂ hj₁ hu₁ hi j' rtr₁' rtr₂' hu₂ hl₁' hl₂' hc₂ hp₂ hr₂ hj₂ => 
    apply ext
    simp only [hp₁, hr₁] at hp₂ hr₂
    simp only [hp₂, hr₂]
    simp [update_unique_aux₅ hc₁ hc₂]
    apply Finmap.ext
    intro x
    -- The cases on h₂ might also have to be an induction.
    by_cases hc : x = j
    case pos => 
      sorry
    case neg =>
      have H := hj₁ x hc
      -- hj₂ uses j' not j

  -- if one is a top and one a nest, then in the top-case the ID i
  -- identifies something at the top level, and in the nest case it doesnt.
  -- this cant be the case for the same initial reactor σ.
  case top.nested =>
    exfalso
    sorry
  case nested.top =>
    exfalso
    sorry

end Reactor
