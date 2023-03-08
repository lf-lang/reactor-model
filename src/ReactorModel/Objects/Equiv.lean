import ReactorModel.Objects.Get

open Classical

namespace Reactor

-- TODO: Do we use this relation for more than proving that reactions are preserved?
--
-- NOTE: By this definition two reactors can be structurally equivalent despite having their input
--       and output ports flipped.
--
-- Two reactors are equivalent if they are structurally equal.
inductive Equiv : Reactor → Reactor → Prop where
  | intro : (∀ cmp, (σ₁.cmp? cmp).ids = (σ₂.cmp? cmp).ids) →
            (∀ {i rtr₁ rtr₂}, (σ₁.nest i = some rtr₁) → (σ₂.nest i = some rtr₂) → Equiv rtr₁ rtr₂)
            → Equiv σ₁ σ₂

namespace Equiv

notation σ₁:max " ≈ " σ₂:max => Reactor.Equiv σ₁ σ₂

variable {σ σ₁ σ₂ σ₃ : Reactor}

theorem top : (σ₁ ≈ σ₂) → (∀ cmp, (σ₁.cmp? cmp).ids = (σ₂.cmp? cmp).ids) 
  | intro h _ => h

theorem nest : (σ₁ ≈ σ₂) → (∀ {i : ID}, (σ₁.nest i = some rtr₁) → (σ₂.nest i = some rtr₂) → rtr₁ ≈ rtr₂) 
  | intro _ h => h

theorem top' : (σ₁ ≈ σ₂) → (σ₁.ids = σ₂.ids) := by
  intro he
  induction he
  case intro ht _ hi =>
    ext cmp i
    simp [ids_mem_iff_obj?]
    constructor <;> (
      intro ⟨o, ho⟩
      cases obj?_decomposition' ho
      case inl hc =>
        have hm := Finmap.mem_ids_iff.mpr ⟨_, hc⟩
        first | rw [ht cmp] at hm | rw [←ht cmp] at hm
        have ⟨_, hm⟩ := Finmap.mem_ids_iff.mp hm
        exact ⟨_, cmp?_to_obj? hm⟩
      case inr hc =>
        have ⟨_, _, hc, ho'⟩ := hc
        have hm := Finmap.mem_ids_iff.mpr ⟨_, hc⟩
        first | rw [ht .rtr] at hm | rw [←ht .rtr] at hm
        have ⟨_, hm⟩ := Finmap.mem_ids_iff.mp hm
        first | specialize hi hc hm | specialize hi hm hc
        have h' := ids_mem_iff_obj?.mpr ⟨_, ho'⟩
        first | rw [ hi] at h' | rw [←hi] at h'
        have ⟨_, h'⟩ := ids_mem_iff_obj?.mp h'
        exact ⟨_, obj?_nest hm h'⟩
    )

theorem nest' : 
  (σ₁ ≈ σ₂) → (σ₁[.rtr][i] = some rtr₁) → (σ₂[.rtr][i] = some rtr₂) → (rtr₁ ≈ rtr₂) := by
  intro he ho₁ ho₂
  induction he
  case intro hi =>
    sorry

theorem con?_id_eq {cmp} : 
  (σ₁ ≈ σ₂) → (σ₁.con? cmp i = some c₁) → (σ₂.con? cmp i = some c₂) → (c₁.id = c₂.id) :=
  sorry

theorem con?_obj_equiv {cmp} :
  (σ₁ ≈ σ₂) → (σ₁.con? cmp i = some c₁) → (σ₂.con? cmp i = some c₂) → (c₁.obj ≈ c₂.obj) := by
  intro he hc₁ hc₂
  have h₁ := con?_to_rtr_obj? hc₁
  have h₂ := con?_to_rtr_obj? hc₂
  have := con?_to_obj?_and_cmp? hc₁
  rw [he.con?_id_eq hc₁ hc₂] at h₁
  exact he.nest' h₁ h₂

-- TODO: Rename this to obj?_some_iff
theorem obj?_iff {cmp} {i : ID} : 
  (σ₁ ≈ σ₂) → ((∃ o₁, σ₁[cmp][i] = some o₁) ↔ (∃ o₂, σ₂[cmp][i] = some o₂)) := by 
  intro he
  constructor <;> (
    intro ho
    sorry
    -- simp [←ids_mem_iff_obj?, ←he.top] at *
    -- exact ho
  )

theorem obj?_none_iff {cmp} {i : ID} (e : σ₁ ≈ σ₂) : 
    (σ₁[cmp][i] = none) ↔ (σ₂[cmp][i] = none) := by 
  sorry

theorem cmp?_iff {cmp} {j : ID} :
  (σ₁ ≈ σ₂) → (σ₁[.rtr][i] = some rtr₁) → (σ₂[.rtr][i] = some rtr₂) → 
  ((∃ o₁, rtr₁.cmp? cmp j = some o₁) ↔ (∃ o₂, rtr₂.cmp? cmp j = some o₂)) := by
  sorry

@[simp]
protected theorem refl : σ ≈ σ :=
  .intro (λ _ => rfl) (by
    intro _ _ _ h₁ h₂
    have := h₁.symm.trans h₂ |> Option.some_inj.mp
    rw [this]
    sorry -- How do you apply induction here?
  )

protected theorem symm : (σ₁ ≈ σ₂) → (σ₂ ≈ σ₁) := by
  sorry

protected theorem trans : (σ₁ ≈ σ₂) → (σ₂ ≈ σ₃) → (σ₁ ≈ σ₃) := by
  intro h₁₂ h₂₃
  induction h₁₂
  case intro hi =>
    sorry

-- For equivalent reactors, obj?-equality propagates to nested reactors.
theorem eq_obj?_nest {cmp} {i : ID} :
  (σ₁ ≈ σ₂) → (σ₁[cmp][i] = σ₂[cmp][i]) → 
  (σ₁[.rtr][j] = some rtr₁) → (σ₂[.rtr][j] = some rtr₂) → 
  rtr₁[cmp][i] = rtr₂[cmp][i] := by
  intro he ho hr₁ hr₂ 
  cases j
  case root => simp at hr₁ hr₂; simp [←hr₁, ←hr₂, ho]
  case nest =>
    have he' := he.nest' hr₁ hr₂
    cases hc : σ₁[cmp][i] <;> rw [hc] at ho
    case none => rw [obj?_not_sub hr₁ hc, obj?_not_sub hr₂ ho.symm]
    case some =>
      cases obj?_decomposition hc
      case inl hc => 
        have ⟨_, hc'⟩ := (cmp?_iff he obj?_self obj?_self).mp ⟨_, hc⟩
        rw [obj?_unique hc hr₁, obj?_unique hc' hr₂]
      case inr _ _ =>
        sorry

theorem obj?_ext {cmp} :
  (σ₁ ≈ σ₂) → (∀ i ∈ (σ₁.cmp? cmp).ids, σ₁[cmp][i] = σ₂[cmp][i]) → (σ₁.cmp? cmp = σ₂.cmp? cmp) := by
  intro he h
  ext i o
  specialize h i
  constructor
  all_goals
    intro ho
    have hm := Finmap.mem_ids_iff.mpr ⟨_, ho⟩
    have hs := Reactor.cmp?_to_obj? ho
    first | rw [h hm] at hs   | skip -- rw [←h hm] at hs
    first | rw [he.top] at hm | skip -- rw [←he.top] at hm
    sorry -- exact Reactor.obj?_and_local_mem_to_cmp? hs hm

theorem obj?_ext' : (σ₁ ≈ σ₂) → (∀ cmp (i : ID), (cmp ≠ .rtr) → σ₁[cmp][i] = σ₂[cmp][i]) → (σ₁ = σ₂) := by
  intro he ho
  induction σ₁ using Reactor.nest_ind generalizing σ₂
  all_goals (
    apply Reactor.ext
    refine ⟨?ports, ?acts, ?state, ?rcns, ?_⟩
    case ports => exact he.obj?_ext (cmp := .prt) (by simp [ho])
    case acts =>  exact he.obj?_ext (cmp := .act) (by simp [ho])
    case state => exact he.obj?_ext (cmp := .stv) (by simp [ho])
    case rcns =>  exact he.obj?_ext (cmp := .rcn) (by simp [ho])
  )
  case base σ₁ h =>
    rw [h] 
    ext1 i
    by_contra hc
    simp at hc
    rw [←Ne.def] at hc
    -- have hi := Finmap.ids_def.mpr hc.symm
    -- have hn := he.top .rtr
    -- simp [h] at hn
    -- simp [←hn] at hi
    sorry
  case step σ₁ hi =>
    apply Finmap.ext
    intro i
    cases hn₁ : σ₁.nest i
    case none =>
      rw [←Option.not_isSome_iff_eq_none, Option.isSome_iff_exists] at hn₁
      have hi₁ := (mt Finmap.mem_ids_iff.mp) hn₁
      rw [he.top .rtr] at hi₁
      have hi₂ := (mt Finmap.mem_ids_iff.mpr) hi₁
      rw [←Option.isSome_iff_exists, Option.not_isSome_iff_eq_none] at hi₂
      simp [hi₂]
      sorry
    case some n₁ =>
      have hn := Finmap.mem_ids_iff.mpr ⟨_, hn₁⟩
      rw [he.top .rtr] at hn
      have ⟨n₂, hn₂⟩ := Finmap.mem_ids_iff.mp hn
      simp [cmp?] at hn₂
      simp [hn₂]
      apply hi n₁ (Finmap.mem_values_iff.mpr ⟨_, hn₁⟩) (he.nest hn₁ hn₂)
      intro cmp i' hc
      exact eq_obj?_nest he (ho cmp i' hc) (cmp?_to_obj? hn₁) (cmp?_to_obj? hn₂)

end Equiv
end Reactor