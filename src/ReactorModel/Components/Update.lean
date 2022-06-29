import ReactorModel.Components.Equiv

open Classical

namespace Reactor

-- Note, this only applies restrictions to the top level of the given reactor.
-- Nested components are addressed by the Update relation.
def EqModID (σ₁ σ₂ : Reactor) (cmp : Cmp) (i : ID) : Prop :=
  ∀ (cmp' i'), (cmp' ≠ cmp ∨ i' ≠ i) → σ₁.cmp? cmp' i' = σ₂.cmp? cmp' i'

notation σ₁:max " %[" cmp ":" i "]= " σ₂:max => EqModID σ₁ σ₂ cmp i

theorem EqModID.ne_id_eq {σ₁ σ₂ : Reactor} {cmp : Cmp} {i i' : ID} :
  (σ₁ %[cmp:i]= σ₂) → (i' ≠ i) → σ₁.cmp? cmp i' = σ₂.cmp? cmp i' :=
  λ he hi => match cmp with | _ => he _ _ (Or.inr hi)

theorem EqModID.ne_cmp_eq {σ₁ σ₂ : Reactor} {cmp cmp' : Cmp} {i : ID} :
  (σ₁ %[cmp:i]= σ₂) → (cmp' ≠ cmp) → σ₁.cmp? cmp' = σ₂.cmp? cmp' := by
  intro he hc
  cases cmp <;> (
    apply Finmap.ext
    intro i
    exact he _ i (Or.inl hc)
  )

-- TODO: Perhaps redefine EqModID in terms of con? or obj? or something?
--       Maybe this would yield a simpler definition of Update as well?
--
-- E.g.:
-- But we can't express mutations this way:
-- structure Update' (σ₁ σ₂ : Reactor) (cmp : Cmp) (i : ID) (o : cmp.type) : Prop :=
--   equiv : σ₁ ≈ σ₂
--   target : σ₂.obj? cmp i = o
--   objs : ∀ (cmp' i'), (cmp' ≠ cmp ∨ i' ≠ i) → σ₁.obj? cmp' i' = σ₂.obj? cmp' i'
theorem EqModID.preserves_Equiv : (σ₁ %[cmp:i]= σ₂) → (cmp ≠ .rtr) → σ₁ ≈ σ₂ := by
  sorry

theorem EqModID.trans {σ₁ σ₂ σ₃ : Reactor} {cmp : Cmp} {i : ID} :
  (σ₁ %[cmp:i]= σ₂) → (σ₂ %[cmp:i]= σ₃) → σ₁ %[cmp:i]= σ₃ :=
  λ h₁₂ h₂₃ cmp' i' hn => (h₁₂ _ _ hn).trans $ h₂₃ _ _ hn
  
-- TODO: Find out how to solve the case distinction more concisely.
theorem EqModID.eq_from_eq_val_for_id {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} 
  (he₁ : σ %[cmp:i]= σ₁) (he₂ : σ %[cmp:i]= σ₂) :
  (σ₁.cmp? cmp i = σ₂.cmp? cmp i) → σ₁ = σ₂ := by
  intro ha
  apply ext
  have h_aux₁ : σ₁.cmp? cmp = σ₂.cmp? cmp := by
    apply Finmap.ext
    intro i'
    by_cases hc : i' = i
    case pos => simp only [hc, ha]
    case neg => simp only [he₁.ne_id_eq hc, (he₂.ne_id_eq hc).symm]
  have h_aux₂ : ∀ cmp', cmp' ≠ cmp → σ₁.cmp? cmp' = σ₂.cmp? cmp' := by
    intro cmp' hn
    have h := he₁.ne_cmp_eq hn
    rw [he₂.ne_cmp_eq hn] at h
    exact h.symm
  cases cmp
  case a.rtr =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ .prt (by intro; contradiction)
    have h₂ := h_aux₂ .rcn (by intro; contradiction)
    have h₃ := h_aux₂ .act (by intro; contradiction)
    have h₄ := h_aux₂ .stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.rcn =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ .prt (by intro; contradiction)
    have h₂ := h_aux₂ .rtr (by intro; contradiction)
    have h₃ := h_aux₂ .act (by intro; contradiction)
    have h₄ := h_aux₂ .stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.prt =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ .rtr (by intro; contradiction)
    have h₂ := h_aux₂ .rcn (by intro; contradiction)
    have h₃ := h_aux₂ .act (by intro; contradiction)
    have h₄ := h_aux₂ .stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.act =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ .prt (by intro; contradiction)
    have h₂ := h_aux₂ .rtr (by intro; contradiction)
    have h₃ := h_aux₂ .rcn (by intro; contradiction)
    have h₄ := h_aux₂ .stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.stv =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ .prt (by intro; contradiction)
    have h₂ := h_aux₂ .rtr (by intro; contradiction)
    have h₃ := h_aux₂ .rcn (by intro; contradiction)
    have h₄ := h_aux₂ .act (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]

inductive Update (cmp : Cmp) (i : ID) (u : cmp.type → cmp.type → Prop) : Reactor → Reactor → Prop :=
  | top {σ₁ σ₂ v v'} :
    (σ₁ %[cmp:i]= σ₂) →
    (σ₁.cmp? cmp i = some v) →
    (σ₂.cmp? cmp i = some v') → 
    (u v v') → 
    Update cmp i u σ₁ σ₂
  | nest {σ₁ σ₂ j rtr₁ rtr₂} : 
    (σ₁ %[Cmp.rtr:j]= σ₂) →
    (σ₁.nest j = some rtr₁) →
    (σ₂.nest j = some rtr₂) →
    (Update cmp i u rtr₁ rtr₂) →
    Update cmp i u σ₁ σ₂

notation σ₁:max " -[" cmp ";" i:max u "]→ " σ₂:max => Reactor.Update cmp i u σ₁ σ₂

set_option quotPrecheck false in
notation σ₁:max " -[" cmp ":" i:max f "]→ " σ₂:max => Reactor.Update cmp i (λ v v' => v' = f v) σ₁ σ₂

theorem Update.requires_lineage_to_target {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {u : cmp.type → cmp.type → Prop} (h : σ₁ -[cmp;i u]→ σ₂) : Nonempty (Lineage σ₁ cmp i) := by
  induction h
  case top ha _ _ => exact ⟨Lineage.end cmp $ Finmap.ids_def'.mpr ⟨_, ha⟩⟩
  case nest hn _ _ hi => exact ⟨Lineage.nest hi.some hn⟩

theorem Update.obj?_target {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {u : cmp.type → cmp.type → Prop} (h : σ₁ -[cmp;i u]→ σ₂) : ∃ o, σ₁.obj? cmp i = some o := by
  sorry

theorem Update.preserves_lineage_to_target {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {u : cmp.type → cmp.type → Prop} (h : σ₁ -[cmp;i u]→ σ₂) : Nonempty (Lineage σ₂ cmp i) := by
  induction h
  case top ha _ => exact ⟨Lineage.end cmp $ Finmap.ids_def'.mpr ⟨_, ha⟩⟩
  case nest hn _ hi => exact ⟨Lineage.nest hi.some hn⟩

theorem Update.unique {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {u : cmp.type → cmp.type → Prop} :
  (σ -[cmp;i u]→ σ₁) → (σ -[cmp;i u]→ σ₂) → (∀ v v₁ v₂, u v v₁ → u v v₂ → v₁ = v₂) → σ₁ = σ₂ := by
  intro h₁ h₂ hu
  (induction h₁ generalizing σ₂) <;> cases h₂
  case top.top he₁ hv₁ hv₁' hu₁ _ _ hu₂ hv₂ hv₂' he₂ => 
    rw [hv₁, Option.some_inj] at hv₂
    rw [hv₂] at hu₁
    rw [hu _ _ _ hu₁ hu₂, ←hv₂'] at hv₁'
    exact EqModID.eq_from_eq_val_for_id he₁ he₂ hv₁'
  case nest.nest σ σ₁ j rtr₁ rtr₂ he₁ hn₁ hn₂ hu₁ hi j' rtr₁' rtr₂' hu₂ hn₁' hn₂' he₂ =>     
    let l₁ := Classical.choice hu₁.requires_lineage_to_target
    let l₁' := Classical.choice hu₂.requires_lineage_to_target
    let l₂ := Lineage.nest l₁ hn₁
    let l₂' := Lineage.nest l₁' hn₁'
    injection σ.uniqueIDs l₂ l₂' with hr _ _ hj
    rw [←hr] at hu₂
    have hi' := hi hu₂
    rw [hi', ←hn₂'] at hn₂
    rw [hj] at he₁ hn₂
    exact EqModID.eq_from_eq_val_for_id he₁ he₂ hn₂
  case' top.nest σ₁ _ _ _ _ ht _ _ _ _ _ hu hn _ _, nest.top σ₁ _ _ _ _ _ hn _ hu _ _ _ _ ht _ _ =>
    let l₁ := Lineage.end cmp $ Finmap.ids_def'.mpr ⟨_, ht⟩
    let l₂ := Lineage.nest hu.requires_lineage_to_target.some hn
    have hc := σ₁.uniqueIDs l₁ l₂
    cases cmp <;> contradiction
  
theorem Update.unique' {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {f : cmp.type → cmp.type} :
  (σ -[cmp:i f]→ σ₁) → (σ -[cmp:i f]→ σ₂) → σ₁ = σ₂ :=
  λ h₁ h₂ => Update.unique h₁ h₂ λ _ _ _ hv₁ hv₂ => hv₁.trans hv₂.symm

theorem Update.change {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {u : cmp.type → cmp.type → Prop} :
  (σ₁ -[cmp;i u]→ σ₂) → ∃ v v', (σ₁.obj? cmp i = some v) ∧ (σ₂.obj? cmp i = some v') ∧ (u v v') := by
  intro h
  induction h
  case top hv hv' hu => exact ⟨_, _, Reactor.cmp?_to_obj? hv, Reactor.cmp?_to_obj? hv', hu⟩
  case nest hr₁ hr₂ _ hi =>
    have ⟨_, _, ho₁, ho₂, hu⟩ := hi
    exact ⟨_, _, Reactor.obj?_nest hr₁ ho₁, Reactor.obj?_nest hr₂ ho₂, hu⟩ 

theorem Update.change' {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {f : cmp.type → cmp.type} :
  (σ₁ -[cmp:i f]→ σ₂) → ∃ v, (σ₁.obj? cmp i = some v) ∧ (σ₂.obj? cmp i = f v) := by
  sorry

notation u₂ " ● " u₁ => λ v₁ v₂ => ∃ v, (u₁ v₁ v) ∧ (u₂ v v₂)

theorem Update.compose {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {u₁ u₂ : cmp.type → cmp.type → Prop} :
  (σ -[cmp;i u₁]→ σ₁) → (σ₁ -[cmp;i u₂]→ σ₂) → (σ -[cmp;i (u₂ ● u₁)]→ σ₂) := by
  intro h₁ h₂
  induction h₁ generalizing σ₂ <;> cases h₂
  case top.top σ₁ σ₂ v₁ v₁' he₁ hv₁ hv₁' hu₁ v₂ v₂' hu₂ hv₂ hv₂' he₂ =>
    rw [hv₁', Option.some_inj] at hv₂
    rw [hv₂] at hu₁
    exact Update.top (he₁.trans he₂) hv₁ hv₂' ⟨v₂, hu₁, hu₂⟩
  case top.nest hv' _ _ _ _ hu hn _ _ =>
    let l₁ := Lineage.end cmp $ Finmap.ids_def'.mpr ⟨_, hv'⟩
    let l₂ := Lineage.nest hu.requires_lineage_to_target.some hn
    have hc := Reactor.uniqueIDs l₁ l₂
    cases cmp <;> contradiction
  case nest.top hn hu _ _ _ _ hv _ _ =>
    let l₁ := Lineage.end cmp $ Finmap.ids_def'.mpr ⟨_, hv⟩
    let l₂ := Lineage.nest hu.preserves_lineage_to_target.some hn
    have hc := Reactor.uniqueIDs l₁ l₂
    cases cmp <;> contradiction
  case nest.nest σ σ₁ j₁ rtr₁₁ rtr₁₂ he₁ hn₁₁ hn₁₂ hu₁ hi j₂ rtr₂₁ rtr₂₂ hu₂ hn₂₁ hn₂₂ he₂ =>
    let l₁ := Lineage.nest hu₁.preserves_lineage_to_target.some hn₁₂
    let l₂ := Lineage.nest hu₂.requires_lineage_to_target.some hn₂₁
    injection σ₁.uniqueIDs l₁ l₂ with hr _ _ hj
    rw [hj] at hn₁₁ he₁
    rw [hr] at hi
    exact Update.nest (he₁.trans he₂) hn₁₁ hn₂₂ (hi hu₂)

theorem Update.compose' {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {f₁ f₂ : cmp.type → cmp.type} :
  (σ -[cmp:i f₁]→ σ₁) → (σ₁ -[cmp:i f₂]→ σ₂) → (σ -[cmp:i (f₂ ∘ f₁)]→ σ₂) := by
  intro h₁ h₂
  have h := Update.compose h₁ h₂
  simp at h
  exact h

theorem Update.funcs_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {cmp : Cmp} {i : ID} {f₁ f₂ : cmp.type → cmp.type} :
  (σ -[cmp:i f₁]→ σ₁) → (σ₁ -[cmp:i f₂]→ σ₁₂) →
  (σ -[cmp:i f₂]→ σ₂) → (σ₂ -[cmp:i f₁]→ σ₂₁) →
  (f₁ ∘ f₂ = f₂ ∘ f₁) → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hc
  have hc₁ := Update.compose' h₁ h₁₂
  have hc₂ := Update.compose' h₂ h₂₁
  rw [hc] at hc₂
  exact Update.unique' hc₁ hc₂

theorem Update.preserves_ne_cmp_or_id {cmp} {f : cmp.type → cmp.type} :
  (σ₁ -[cmp:i f]→ σ₂) → (cmp' ≠ cmp ∨ i' ≠ i) → (cmp ≠ .rtr) → (cmp' ≠ .rtr) → (σ₁.obj? cmp' i' = σ₂.obj? cmp' i') := by
  intro h ho hr hr'
  induction h
  case top he _ _ _ =>
    have H := he _ _ ho
    sorry -- Argument about lineages and EqModID.
  case nest he _ _ _ hi =>
    -- have H := he _ _ ho
    sorry

-- TODO: Cf. comment on EqModID.preserves_Equiv.
theorem Update.preserves_Equiv {cmp} {u : cmp.type → cmp.type → Prop} : (σ₁ -[cmp;i u]→ σ₂) → (cmp ≠ .rtr) → σ₁ ≈ σ₂ := by
  sorry

structure Mutation.rtrRel (cmp : Cmp) (cmpRel : (ID ⇉ cmp.type) → (ID ⇉ cmp.type) → Prop) (σ₁ σ₂ : Reactor) : Prop where
  eqCmps : ∀ cmp', (cmp' ≠ cmp) → σ₁.cmp? cmp' = σ₂.cmp? cmp'
  mutate : cmpRel (σ₁.cmp? cmp) (σ₂.cmp? cmp)

open Mutation in
inductive Mutation (σ₁ σ₂ : Reactor) (cmp : Cmp) (cmpRel : (ID ⇉ cmp.type) → (ID ⇉ cmp.type) → Prop) : Rooted ID → Prop
  | root : (rtrRel cmp cmpRel) σ₁ σ₂ → Mutation σ₁ σ₂ cmp cmpRel ⊤ 
  | nest {i} : σ₁ -[Cmp.rtr;i (rtrRel cmp cmpRel)]→ σ₂ → Mutation σ₁ σ₂ cmp cmpRel (Rooted.nest i) 

notation σ₁:max " -[" cmp:max "/" r:max cmpRel "]→ " σ₂:max => Reactor.Mutation σ₁ σ₂ cmp cmpRel r

set_option quotPrecheck false in
notation σ₁:max " -[" cmp:max "|" r:max f "]→ " σ₂:max => Reactor.Mutation σ₁ σ₂ cmp (λ c c' => c' = f c) r

end Reactor