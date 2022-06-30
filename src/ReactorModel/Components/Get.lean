import ReactorModel.Components.Reactor.Proper

open Classical

namespace Reactor

namespace Lineage

-- The "parent" in a lineage is the reactor which contains the target of the lineage.
-- This function returns that reactor along with its ID.
-- If the direct parent is the top-level reactor `σ`, then the ID is `⊤`.
def container : Lineage σ cmp i → Identified Reactor 
  | .nest l@(.nest ..) _ => l.container
  | @nest r j .. =>         { id := j, obj := r }
  | _ =>                    { id := ⊤, obj := σ }

theorem end_container_eq_root {cmp} (h : i ∈ (σ.cmp? cmp).ids) : (Lineage.end cmp h).container.obj = σ := by
  simp [Lineage.container]

theorem nest_container_obj {σ rtr : Reactor} (l : Lineage rtr cmp i) (h : σ.nest j = rtr) : (Lineage.nest l h).container.obj = l.container.obj := by
  cases l <;> simp [container]

theorem container_cmp_mem (l : Lineage σ cmp i) : ∃ o, l.container.obj.cmp? cmp i = some o := by
  induction l
  case «end» _ h => simp [container, Finmap.ids_def'.mp h]
  case nest hi => simp [nest_container_obj, hi]

theorem nest_container_id_not_top {σ rtr : Reactor} (l : Lineage rtr cmp i) (h : σ.nest j = rtr) : (Lineage.nest l h).container.id ≠ ⊤ := by
  by_contra hc
  induction l generalizing σ j <;> simp [container] at hc
  case nest hn hi => exact hi hn hc

theorem nest_container_id 
  {σ rtr₁ rtr₂ : Reactor} {l₁ : Lineage rtr₁ cmp i₁} {l₂ : Lineage rtr₂ cmp i₂} 
  {h₁ : σ.nest j₁ = rtr₁} {h₂ : σ.nest j₂ = rtr₂} : 
  ((Lineage.nest l₁ h₁).container.id = (Lineage.nest l₂ h₂).container.id) → 
  l₁.container.id = l₂.container.id := by 
  intro hi
  cases l₁ <;> cases l₂
  case end.end => simp [container]
  case end.nest hm₁ rtr₂ j₂ hn₂ l₂ => 
    exfalso
    simp [container] at hi
    sorry
  case nest.end => sorry
  case nest.nest => simp_all [container]

theorem container_eq_id_eq_obj {l₁ : Lineage σ cmp i₁} {l₂ : Lineage σ cmp i₂} : (l₁.container.id = l₂.container.id) → l₁.container = l₂.container := by
  intro hi
  induction l₁ <;> cases l₂ <;> (simp [container] at *)
  case end.nest hn l =>     exact absurd hi.symm (l.nest_container_id_not_top hn)
  case nest.end l hn _ _ => exact absurd hi      (l.nest_container_id_not_top hn)
  case nest.nest rtr₁ _ _ j₁ _ l₁ hn₁ h rtr₂ j₂ hn₂ l₂ =>
    suffices hj : j₁ = j₂ by
      subst hj
      have hr := hn₁.symm.trans hn₂ |> Option.some_inj.mp
      subst hr
      apply Identified.ext _ _ hi
      simp [nest_container_obj, h (nest_container_id hi)]
    sorry

end Lineage

-- Note, as we have `Reactor.uniqueIDs`, the choice in `h.some` is always unique.
noncomputable def con? (σ : Reactor) (cmp : Cmp) (i : ID) : Option (Identified Reactor) := 
  if h : Nonempty (Lineage σ cmp i) then h.some.container else none

theorem con?_def : 
  (σ.con? cmp i = some c) ↔ (∃ l : Lineage σ cmp i, l.container = c) := by
  rw [con?]
  split <;> simp
  case inl h => exact ⟨λ _ => ⟨h.some, by simp_all⟩, λ ⟨l, hl⟩ => by simp [σ.uniqueIDs h.some l, hl]⟩
  case inr h => exact (λ l => absurd (Nonempty.intro l) h  )      

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
  have ⟨l, hl⟩ := con?_def.mp h
  have ⟨o, ho⟩ := l.container_cmp_mem
  rw [hl] at ho
  exact ⟨o, Option.bind_eq_some.mpr ⟨_, h, ho⟩, ho⟩    

theorem con?_and_cmp?_to_obj? : 
  (σ.con? cmp i = some c) → (c.obj.cmp? cmp i = some o) → (σ.obj? cmp i = some o) := by
  intro hc hm
  have ⟨_, ho, hm'⟩ := con?_to_obj?_and_cmp? hc
  simp [hm.symm.trans hm', ho]

theorem con?_to_rtr_obj? :
  (σ.con? cmp i = some c) → (σ.obj? .rtr c.id = some c.obj) := by
  intro h
  have ⟨l, hl⟩ := con?_def.mp h
  sorry

theorem con?_eq_id_to_eq :
  (σ.con? cmp i₁ = some c₁) → (σ.con? cmp i₂ = some c₂) → (c₁.id = c₂.id) → c₁ = c₂ := by
  intro hc₁ hc₂ hi
  unfold con? at hc₁ hc₂
  by_cases hl₁ : Nonempty (Lineage σ cmp i₁) <;> 
  by_cases hl₂ : Nonempty (Lineage σ cmp i₂) <;>
  simp [hl₁, hl₂] at hc₁ hc₂
  case pos =>
    set l₁ := hl₁.some
    set l₂ := hl₂.some
    cases h₁ : l₁ <;> cases h₂ : l₂ <;> (simp [h₁, h₂, Lineage.container] at hc₁ hc₂)
    case end.end => simp [←hc₁, ←hc₂]
    case end.nest hn l =>
      have h := l.nest_container_id_not_top hn
      simp [hc₂, ←hi, ←hc₁] at h
    case nest.end hn l _ =>
      have h := l.nest_container_id_not_top hn
      simp [hc₁, hi, ←hc₂] at h
    case nest.nest =>
      simp [←hc₁, ←hc₂] at hi
      have h := Lineage.container_eq_id_eq_obj hi
      simp [hc₁, hc₂] at h
      exact h

theorem obj?_and_con?_to_cmp? {i : ID} : 
  (σ.obj? cmp i = some o) → (σ.con? cmp i = some c) → (c.obj.cmp? cmp i = some o) := by
  intro ho hc
  have ⟨_, hc', hm⟩ := obj?_to_con?_and_cmp? ho
  simp [Option.some_inj.mp $ hc.symm.trans hc', hm]

theorem cmp?_to_obj? : (σ.cmp? cmp i = some o) → (σ.obj? cmp i = some o) := by
  intro h
  let l := Lineage.end _ $ Finmap.ids_def'.mpr ⟨_, h⟩
  have h' := con?_def.mpr ⟨l, rfl⟩
  have hc : l.container = σ := Lineage.end_container_eq_root _
  simp [←hc] at h
  exact con?_and_cmp?_to_obj? h' h

theorem obj?_nest {j : ID} : 
  (σ.nest i = some rtr) → (rtr.obj? cmp j = some o) → (σ.obj? cmp j = some o) := by
  intro hn ho
  have ⟨c, hc, hm⟩ := obj?_to_con?_and_cmp? ho
  have ⟨l, hl⟩ := con?_def.mp hc
  apply con?_and_cmp?_to_obj?
  · exact con?_def.mpr ⟨Lineage.nest l hn, rfl⟩
  · simp [Lineage.nest_container_obj l hn, hm, hl]

theorem obj?_sub {i j : ID} : 
  (σ.obj? .rtr i = some rtr) → (rtr.obj? cmp j = some o) → (σ.obj? cmp j = some o) := by
  intro hr hc
  have hc' := hc
  have ⟨c, hc, hmc⟩ := obj?_to_con?_and_cmp? hc
  have ⟨r, hr, hmr⟩ := obj?_to_con?_and_cmp? hr
  have := con?_def.mp hc
  have := con?_def.mp hr
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
    exact ⟨_, (obj?_to_con?_and_cmp? h).choose_spec.left⟩
  case mpr =>
    have ⟨_, h, _⟩ := con?_to_obj?_and_cmp? h.choose_spec
    exact ⟨_, Finmap.ids_def'.mpr ⟨_, h⟩, by simp [Rooted.nest?]⟩  

theorem ids_mem_iff_obj? : (i ∈ σ.ids cmp) ↔ (∃ o, σ.obj? cmp i = some o) := by
  simp [←contains_iff_obj?, ids_mem_iff_contains]

theorem obj?_and_local_mem_to_cmp? {i : ID} : 
  (σ.obj? cmp i = some o) → (i ∈ (σ.cmp? cmp).ids) → (σ.cmp? cmp i = some o) := by
  intro ho hi
  have ⟨c, hc, hm⟩ := obj?_to_con?_and_cmp? ho
  rw [←hm]
  suffices h : σ = c.obj by simp [h]
  have ⟨l, hl⟩ := con?_def.mp hc
  have hm := Finmap.ids_def'.mpr ⟨_, hm⟩
  simp [←Lineage.end_container_eq_root hm, ←Lineage.end_container_eq_root hi]
  sorry

end Reactor