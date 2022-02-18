import ReactorModel.Components.Get

open Classical

namespace Reactor

-- Note, this only makes sense when talking about a top-level ID.
def EqModID (σ₁ σ₂ : Reactor) (cmp : Cmp) (i : ID) : Prop :=
  ∀ (cmp' i'), (cmp' ≠ cmp ∨ i' ≠ i) → σ₁.cmp cmp' i' = σ₂.cmp cmp' i'

notation σ₁:max " %[" cmp ":" i "]= " σ₂:max => EqModID σ₁ σ₂ cmp i

theorem EqModID.ne_id_eq {σ₁ σ₂ : Reactor} {cmp : Cmp} {i i' : ID} :
  (σ₁ %[cmp:i]= σ₂) → (i' ≠ i) → σ₁.cmp cmp i' = σ₂.cmp cmp i' :=
  λ he hi => match cmp with | _ => he _ _ (Or.inr hi)

theorem EqModID.ne_cmp_eq {σ₁ σ₂ : Reactor} {cmp cmp' : Cmp} {i : ID} :
  (σ₁ %[cmp:i]= σ₂) → (cmp' ≠ cmp) → σ₁.cmp cmp' = σ₂.cmp cmp' := by
  intro he hc
  cases cmp <;> (
    apply Finmap.ext
    intro i
    exact he _ i (Or.inl hc)
  )

theorem EqModID.trans {σ₁ σ₂ σ₃ : Reactor} {cmp : Cmp} {i : ID} :
  (σ₁ %[cmp:i]= σ₂) → (σ₂ %[cmp:i]= σ₃) → σ₁ %[cmp:i]= σ₃ :=
  λ h₁₂ h₂₃ cmp' i' hn => (h₁₂ _ _ hn).trans $ h₂₃ _ _ hn
  
-- TODO: Find out how to solve the case distinction more concisely.
theorem EqModID.eq_from_eq_val_for_id {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} 
  (he₁ : σ %[cmp:i]= σ₁) (he₂ : σ %[cmp:i]= σ₂) :
  (σ₁.cmp cmp i = σ₂.cmp cmp i) → σ₁ = σ₂ := by
  intro ha
  apply ext
  have h_aux₁ : σ₁.cmp cmp = σ₂.cmp cmp := by
    apply Finmap.ext
    intro i'
    by_cases hc : i' = i
    case pos => simp only [hc, ha]
    case neg => simp only [he₁.ne_id_eq hc, Eq.symm $ he₂.ne_id_eq hc]
  have h_aux₂ : ∀ cmp', cmp' ≠ cmp → σ₁.cmp cmp' = σ₂.cmp cmp' := by
    intro cmp' hn
    have h := he₁.ne_cmp_eq hn
    rw [he₂.ne_cmp_eq hn] at h
    exact Eq.symm h
  cases cmp
  case a.rtr =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rcn (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.prt (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.act (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄] 
  case a.rcn =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rtr (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.prt (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.act (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.prt =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rtr (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.rcn (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.act (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.act =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rtr (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.prt (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.rcn (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.stv =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rtr (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.prt (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.rcn (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.act (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]

inductive Update (cmp : Cmp) (i : ID) (f : cmp.type → cmp.type) : Reactor → Reactor → Prop :=
  | top {σ₁ σ₂ v} :
    (σ₁ %[cmp:i]= σ₂) →
    (σ₁.cmp cmp i = some v) → -- This is required so that we know where to actually update i / so that there's at most one possible outcome of an update. 
    (σ₂.cmp cmp i = f v) → 
    Update cmp i f σ₁ σ₂
  | nested {σ₁ σ₂} {j rtr₁ rtr₂} : 
    (σ₁ %[Cmp.rtr:j]= σ₂) →
    (σ₁.nest j = some rtr₁) →
    (σ₂.nest j = some rtr₂) →
    (Update cmp i f rtr₁ rtr₂) →
    Update cmp i f σ₁ σ₂

notation σ₁:max " -[" cmp ":" i:max f "]→ " σ₂:max => Reactor.Update cmp i f σ₁ σ₂

theorem Update.requires_lineage_to_target₁ {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {f : cmp.type → cmp.type} (h : σ₁ -[cmp:i f]→ σ₂) : Nonempty (Lineage σ₁ i) := by
  induction h
  case top ha _ => exact ⟨Lineage.fromCmp cmp $ Finmap.ids_def'.mpr ⟨_, ha.symm⟩⟩
  case nested hn _ _ hi => exact ⟨Lineage.nest _ _ hi.some hn⟩

theorem Update.requires_lineage_to_target₂ {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {f : cmp.type → cmp.type} (h : σ₁ -[cmp:i f]→ σ₂) : Nonempty (Lineage σ₂ i) := by
  induction h
  case top ha => exact ⟨Lineage.fromCmp cmp $ Finmap.ids_def'.mpr ⟨_, ha.symm⟩⟩
  case nested hn _ hi => exact ⟨Lineage.nest _ _ hi.some hn⟩

theorem Update.unique {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {f : cmp.type → cmp.type} :
  (σ -[cmp:i f]→ σ₁) → (σ -[cmp:i f]→ σ₂) → σ₁ = σ₂ := by
  intro h₁ h₂
  (induction h₁ generalizing σ₂) <;> cases h₂
  case top.top he₁ hv₁ hi₁ _ hv₂ hi₂ he₂ => 
    rw [hv₁, Option.some_inj] at hv₂
    rw [hv₂, ←hi₂] at hi₁
    exact EqModID.eq_from_eq_val_for_id he₁ he₂ hi₁
  case nested.nested σ σ₁ j rtr₁ rtr₂ he₁ hn₁ hn₂ hu₁ hi j' rtr₁' rtr₂' hu₂ hn₁' hn₂' he₂ =>     
    let l₁ := Classical.choice hu₁.requires_lineage_to_target₁
    let l₁' := Classical.choice hu₂.requires_lineage_to_target₁
    let l₂ := Lineage.nest _ _ l₁ hn₁
    let l₂' := Lineage.nest _ _ l₁' hn₁'
    injection σ.uniqueIDs l₂ l₂' with _ hr _ hj
    rw [←hr] at hu₂
    have hi' := hi hu₂
    rw [hi', ←hn₂'] at hn₂
    rw [hj] at he₁ hn₂
    exact EqModID.eq_from_eq_val_for_id he₁ he₂ hn₂
  case' top.nested σ₁ _ _ _ ht _ _ _ _ hu hn _ _, nested.top σ₁ _ _ _ _ _ hn _ hu _ _ ht _ _ =>
    let l₁ := Lineage.fromCmp cmp $ Finmap.ids_def'.mpr ⟨_, ht.symm⟩
    let l₂ := Lineage.nest _ _ hu.requires_lineage_to_target₁.some hn
    have hc := σ₁.uniqueIDs l₁ l₂
    cases cmp <;> contradiction
  
theorem Update.reflects_in_objFor {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {f : cmp.type → cmp.type} :
  (σ₁ -[cmp:i f]→ σ₂) → ∃ v, σ₁ *[cmp, i]= v ∧ σ₂ *[cmp, i]= (f v) := by
  intro h
  induction h
  case top σ₁ σ₂ v _ hv hf =>
    simp only [objFor]
    exists v
    constructor
    case left =>
      use Lineage.fromCmp cmp $ Finmap.ids_def'.mpr ⟨v, hv.symm⟩
      simp only [←hv]
      sorry -- TODO: This used to work: cases cmp <;> simp only [Lineage.directParent]
    case right =>
      use Lineage.fromCmp cmp $ Finmap.ids_def'.mpr ⟨f v, hf.symm⟩
      simp only [←hf]
      sorry -- TODO: This used to work: cases cmp <;> simp only [Lineage.directParent]
  case nested _ σ₂ j rtr₁ rtr₂ _ hr₁ hr₂ _ hi =>
    simp only [objFor] at *
    have ⟨v, ⟨lv, hv⟩, ⟨lf, hf⟩⟩ := hi
    exists v
    constructor
    case left =>
      use Lineage.nest rtr₁ j lv hr₁
      simp only [←hv]
      sorry -- TODO: This used to work: cases cmp <;> simp only [Lineage.directParent]
    case right =>
      use Lineage.nest rtr₂ j lf hr₂
      simp only [←hf]
      sorry -- TODO: This used to work: cases cmp <;> simp only [Lineage.directParent]

theorem Update.compose {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {f₁ f₂ : cmp.type → cmp.type} :
  (σ -[cmp:i f₁]→ σ₁) → (σ₁ -[cmp:i f₂]→ σ₂) → (σ -[cmp:i (f₂ ∘ f₁)]→ σ₂) := by
  intro h₁ h₂
  induction h₁ generalizing σ₂ <;> cases h₂
  case top.top v₁ he₁ hv₁ hf₁ v₂ hv₂ hf₂ he₂ =>
    rw [hf₁, Option.some_inj] at hv₂
    rw [←hv₂] at hf₂
    exact Update.top (he₁.trans he₂) hv₁ hf₂
  case top.nested σ₁ _ _ _ hf _ _ _ hu hn₁ _ _ =>
    let l₁ := Lineage.fromCmp cmp $ Finmap.ids_def'.mpr ⟨_, hf.symm⟩
    let l₂ := Lineage.nest _ _ hu.requires_lineage_to_target₁.some hn₁
    have hc := σ₁.uniqueIDs l₁ l₂
    cases cmp <;> contradiction
  case nested.top σ σ₁ j rtr₁ rtr₂ he₁ hn₁ hn₂ hu hi v hv hf he₂ =>
    let l₁ := Lineage.fromCmp cmp $ Finmap.ids_def'.mpr ⟨_, hv.symm⟩
    let l₂ := Lineage.nest _ _ hu.requires_lineage_to_target₂.some hn₂
    have hc := σ₁.uniqueIDs l₁ l₂
    cases cmp <;> contradiction
  case nested.nested σ σ₁ j₁ rtr₁₁ rtr₁₂ he₁ hn₁₁ hn₁₂ hu₁ hi j₂ rtr₂₁ rtr₂₂ hu₂ hn₂₁ hn₂₂ he₂ =>
    let l₁ := Lineage.nest _ _ hu₁.requires_lineage_to_target₂.some hn₁₂
    let l₂ := Lineage.nest _ _ hu₂.requires_lineage_to_target₁.some hn₂₁
    injection σ₁.uniqueIDs l₁ l₂ with _ hr _ hj
    rw [hj] at hn₁₁ he₁
    rw [hr] at hi
    apply Update.nested (he₁.trans he₂) hn₁₁ hn₂₂ (hi hu₂)

theorem Update.funcs_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {cmp : Cmp} {i : ID} {f₁ f₂ : cmp.type → cmp.type} :
  (σ -[cmp:i f₁]→ σ₁) → (σ₁ -[cmp:i f₂]→ σ₁₂) →
  (σ -[cmp:i f₂]→ σ₂) → (σ₂ -[cmp:i f₁]→ σ₂₁) →
  (f₁ ∘ f₂ = f₂ ∘ f₁) → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hc
  have hc₁ := Update.compose h₁ h₁₂
  have hc₂ := Update.compose h₂ h₂₁
  rw [hc] at hc₂
  exact Update.unique hc₁ hc₂

theorem Update.ne_cmp_ne_rtr_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {cmp₁ cmp₂ : Cmp} {i₁ i₂ : ID} {f₁ : cmp₁.type → cmp₁.type} {f₂ : cmp₂.type → cmp₂.type} :
  (σ -[cmp₁:i₁ f₁]→ σ₁) → (σ₁ -[cmp₂:i₂ f₂]→ σ₁₂) →
  (σ -[cmp₂:i₂ f₂]→ σ₂) → (σ₂ -[cmp₁:i₁ f₁]→ σ₂₁) →
  (cmp₁ ≠ cmp₂) → (cmp₁ ≠ Cmp.rtr) → (cmp₂ ≠ Cmp.rtr) → 
  σ₁₂ = σ₂₁ :=
  sorry

theorem Update.ne_id_ne_rtr_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {cmp : Cmp} {i₁ i₂ : ID} {f₁ f₂ : cmp.type → cmp.type} :
  (σ -[cmp:i₁ f₁]→ σ₁) → (σ₁ -[cmp:i₂ f₂]→ σ₁₂) →
  (σ -[cmp:i₂ f₂]→ σ₂) → (σ₂ -[cmp:i₁ f₁]→ σ₂₁) →
  (i₁ ≠ i₂) → (cmp ≠ Cmp.rtr) → 
  σ₁₂ = σ₂₁ :=
  sorry

end Reactor

