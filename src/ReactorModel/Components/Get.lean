import ReactorModel.Components.Reactor.Basic

open Classical Port

namespace Reactor

namespace Lineage

-- The "parent" in a lineage is the reactor which contains the target of the lineage.
-- This function returns that reactor along with its ID.
-- If the direct parent is the top-level reactor `σ`, then the ID is `⊤`.
def container : Lineage σ cmp i → Identified Reactor 
  | .nest l@h:(.nest ..) _ => l.container
  | @nest r j .. =>           { id := j, obj := r }
  | _ =>                      { id := ⊤, obj := σ }

theorem end_container_eq_root {cmp} (h : i ∈ (σ.cmp? cmp).ids) : (Lineage.end cmp h).container.obj = σ := by
  simp [Lineage.container]

theorem nest_container_obj {σ rtr : Reactor} (l : Lineage rtr cmp i) (h : σ.nest j = rtr) : (Lineage.nest l h).container.obj = l.container.obj := by
  cases l <;> simp [container]

theorem container_cmp_mem (l : Lineage σ cmp i) : ∃ o, l.container.obj.cmp? cmp i = some o := by
  induction l
  case «end» _ h =>
    have ⟨_, h⟩ := Finmap.ids_def'.mp h
    simp [container, h.symm]
  case nest hi =>
    simp [nest_container_obj, hi]
    
end Lineage

-- The `Container` relation is used to determine whether a given ID `c`
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
-- we could easily extend the definition of `Container` to check whether `i = ⊤`
-- and yield `False` in that case (as the top-level reactor will never have a
-- parent container).
inductive Container (σ : Reactor) (cmp : Cmp) (i : ID) : Identified Reactor → Prop
  | intro (l : Lineage σ cmp i) : Container σ cmp i l.container

-- In the `Container` relation, any given ID can have at most one parent.
theorem Container.unique : (Container σ cmp i c₁) → (Container σ cmp i c₂) → c₁ = c₂
  | ⟨l₁⟩, ⟨l₂⟩ => by simp [eq_of_heq $ σ.uniqueIDs l₁ l₂]

-- NOTE: As we have `Container.unique`, the choice of object is always unique.
noncomputable def con? (σ : Reactor) (cmp : Cmp) (i : ID) : Option (Identified Reactor) := 
  if h : ∃ c, Container σ cmp i c then h.choose else none

theorem Container.iff_con? {cmp} : (Container σ cmp i c) ↔ (σ.con? cmp i = some c) := by
  constructor <;> (intro h; simp [con?] at *) 
  case mp =>
    split
    case inl hc => simp [h.unique hc.choose_spec]
    case inr hc => exact absurd h (not_exists.mp hc $ c)
  case mpr => 
    split at h
    case inl hc => simp at h; rw [←h]; exact hc.choose_spec
    case inr => contradiction

noncomputable def obj? (σ : Reactor) (cmp : Cmp) : (Rooted ID) ⇉ cmp.type := {
  lookup := λ i => 
    match i, cmp with 
    | ⊤, .rtr => σ
    | .nest i, cmp => σ.con? cmp i >>= (·.obj.cmp? cmp i)
    | _, _ => none
  finite := sorry
}

noncomputable def obj?' (σ : Reactor) (cmp : Cmp) : ID ⇉ cmp.type := 
  σ.obj? cmp |>.map' (·.nest?) Rooted.nest?_inj

variable {σ : Reactor} {cmp : Cmp} 

theorem obj?'_eq_obj? {i : ID} : σ.obj?' cmp i = σ.obj? cmp i :=
  Finmap.map'_def rfl

@[simp]
theorem obj?_self : σ.obj? .rtr ⊤ = some σ := by simp [obj?]

theorem obj?_root : (σ.obj? cmp ⊤ = some o) → (cmp = .rtr ∧ HEq o σ) := by 
  intro h
  cases cmp
  case rtr => simp [obj?] at h; simp [h]
  all_goals simp [obj?] at h

theorem obj?_to_con?_and_cmp? {i : ID} : 
  (σ.obj? cmp i = some o) → (∃ c, σ.con? cmp i = some c ∧ c.obj.cmp? cmp i = some o) :=
  Option.bind_eq_some.mp

theorem con?_to_obj?_and_cmp? : 
  (σ.con? cmp i = some c) → (∃ o, σ.obj? cmp i = some o ∧ c.obj.cmp? cmp i = o) := by
  intro h
  cases Container.iff_con?.mpr h
  case intro l =>
    have ⟨o, ho⟩ := l.container_cmp_mem
    exact ⟨o, Option.bind_eq_some.mpr ⟨_, h, ho⟩, ho⟩    

theorem con?_and_cmp?_to_obj? : 
  (σ.con? cmp i = some c) → (c.obj.cmp? cmp i = some o) → (σ.obj? cmp i = some o) := by
  intro hc hm
  have ⟨_, ho, hm'⟩ := con?_to_obj?_and_cmp? hc
  simp [hm.symm.trans hm', ho]

theorem con?_to_rtr_obj? :
  (σ.con? cmp i = some c) → (σ.obj? .rtr c.id = some c.obj) := by
  sorry

theorem obj?_and_con?_to_cmp? {i : ID} : 
  (σ.obj? cmp i = some o) → (σ.con? cmp i = some c) → (c.obj.cmp? cmp i = some o) := by
  intro ho hc
  have ⟨_, hc', hm⟩ := obj?_to_con?_and_cmp? ho
  simp [Option.some_inj.mp $ hc.symm.trans hc', hm]

theorem cmp?_to_obj? : (σ.cmp? cmp i = some o) → (σ.obj? cmp i = some o) := by
  intro h
  let l := Lineage.end _ $ Finmap.ids_def'.mpr ⟨_, h.symm⟩
  have h' := Container.iff_con?.mp $ .intro l
  have hc : l.container = σ := Lineage.end_container_eq_root _
  simp [←hc] at h
  exact con?_and_cmp?_to_obj? h' h

theorem obj?_nest {j : ID} : 
  (σ.nest i = some rtr) → (rtr.obj? cmp j = some o) → (σ.obj? cmp j = some o) := by
  intro hn ho
  have ⟨c, hc, hm⟩ := obj?_to_con?_and_cmp? ho
  cases Container.iff_con?.mpr hc
  case intro l =>
    let l' := Lineage.nest l hn
    have hc' := Container.intro l'
    apply con?_and_cmp?_to_obj?
    · exact Container.iff_con?.mp hc'
    · simp [Lineage.nest_container_obj l hn, hm]

theorem obj?_sub {i j : ID} : 
  (σ.obj? .rtr i = some rtr) → (rtr.obj? cmp j = some o) → (σ.obj? cmp j = some o) := by
  intro hr hc
  have hc' := hc
  have ⟨c, hc, hmc⟩ := obj?_to_con?_and_cmp? hc
  have ⟨r, hr, hmr⟩ := obj?_to_con?_and_cmp? hr
  cases Container.iff_con?.mpr hc <;> cases Container.iff_con?.mpr hr
  case intro.intro lc lr =>
    sorry

-- Note, we could make this an iff by using obj?_sub and cmp?_to_obj? for the other direction.
theorem obj?_decomposition {i : ID} :
  (σ.obj? cmp i = some o) → (σ.cmp? cmp i = some o) ∨ (∃ j rtr, σ.obj? .rtr j = some rtr ∧ rtr.cmp? cmp i = some o) := by
  sorry

theorem obj?_decomposition' {i : ID} :
  (σ.obj? cmp i = some o) → (σ.cmp? cmp i = some o) ∨ (∃ j rtr, σ.nest j = some rtr ∧ rtr.obj? cmp i = some o) := by
  sorry

theorem obj?_unique {i j : ID} : 
  (σ.cmp? cmp i = some o) → (σ.obj? .rtr j = some rtr) → (rtr.obj? cmp i = none) := 
  sorry    

-- Corollary of obj?_sub.
theorem obj?_not_sub : 
  (σ.obj? .rtr i = some rtr) → (σ.obj? cmp j = none) → (rtr.obj? cmp j = none) := 
  sorry 

theorem local_mem_exclusive : 
  (σ.obj? .rtr i₁ = some c₁) → (σ.obj? .rtr i₂ = some c₂) → (i₁ ≠ i₂) →
  (j ∈ (c₁.cmp? cmp).ids) → (j ∉ (c₂.cmp? cmp).ids) := 
  sorry

def contains (σ : Reactor) (cmp : Cmp) (i : ID) : Prop := 
  ∃ c, σ.con? cmp i = some c

theorem contains_iff_obj? : (σ.contains cmp i) ↔ (∃ o, σ.obj? cmp i = some o) := by 
  constructor <;> intro ⟨_, h⟩
  case mp =>  have ⟨_, h, _⟩ := con?_to_obj?_and_cmp? h; exact ⟨_, h⟩
  case mpr => have ⟨_, h, _⟩ := obj?_to_con?_and_cmp? h; exact ⟨_, h⟩

noncomputable def ids (σ : Reactor) (cmp : Cmp) := 
  (σ.obj? cmp).ids.image (·.nest?) |>.erase_none

theorem ids_mem_iff_contains : (i ∈ σ.ids cmp) ↔ (σ.contains cmp i) := by
  constructor <;> (intro h; simp [ids, Finset.mem_erase_none] at *)
  case mp =>
    simp [Finmap.ids_def'] at h
    have ⟨j, ⟨_ , h⟩, hj⟩ := h
    cases j <;> simp [Rooted.nest?] at hj
    rw [←hj]
    exact ⟨_, (obj?_to_con?_and_cmp? h.symm).choose_spec.left⟩
  case mpr =>
    have ⟨_, h, _⟩ := con?_to_obj?_and_cmp? h.choose_spec
    exact ⟨_, Finmap.ids_def'.mpr ⟨_, h.symm⟩, by simp [Rooted.nest?]⟩  

theorem ids_mem_iff_obj? : (i ∈ σ.ids cmp) ↔ (∃ o, σ.obj? cmp i = some o) := by
  simp [←contains_iff_obj?, ids_mem_iff_contains]

theorem obj?_and_local_mem_to_cmp? {i : ID} : 
  (σ.obj? cmp i = some o) → (i ∈ (σ.cmp? cmp).ids) → (σ.cmp? cmp i = some o) := by
  intro ho hi
  have ⟨c, hc, hm⟩ := obj?_to_con?_and_cmp? ho
  rw [←hm]
  suffices h : σ = c.obj by simp [h]
  have ⟨l⟩ := Container.iff_con?.mpr hc
  clear hc
  have hm := Finmap.ids_def'.mpr ⟨_, hm.symm⟩
  simp [←Lineage.end_container_eq_root hm, ←Lineage.end_container_eq_root hi]
  apply congr_arg
  -- TODO: This holds, but has a problem with hm and hi not having the same type.
  sorry

end Reactor