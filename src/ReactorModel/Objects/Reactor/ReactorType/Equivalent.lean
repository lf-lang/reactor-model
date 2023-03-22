import ReactorModel.Objects.Reactor.ReactorType.Updatable

-- TODO: Rename `cmp` to `cm` globally, so there's no clash with `Ord.cmp`.

namespace ReactorType 

inductive Equivalent [ReactorType α] : α → α → Prop
  | intro
    (cmp?_ids_eq : ∀ cmp, (cmp? cmp rtr₁).ids = (cmp? cmp rtr₂).ids) 
    (rcns_some_eq : ∀ {i r₁ r₂}, (rcns rtr₁ i = some r₁) → (rcns rtr₂ i = some r₂) → r₁ = r₂) 
    (nest_equiv : ∀ {i n₁ n₂}, (nest rtr₁ i = some n₁) → (nest rtr₂ i = some n₂) → Equivalent n₁ n₂) 
    : Equivalent rtr₁ rtr₂
 
namespace Equivalent

instance [ReactorType α] : HasEquiv α where 
  Equiv := Equivalent

@[refl]
protected theorem refl [ReactorType.WellFounded α] {rtr : α} : rtr ≈ rtr := by
  induction rtr using ReactorType.WellFounded.induction
  case nest hi =>
    constructor <;> (intros; simp_all)
    exact hi _ _ ‹_›  

variable [ReactorType α] {rtr rtr₁ : α}

@[symm]
protected theorem symm (e : rtr₁ ≈ rtr₂) : rtr₂ ≈ rtr₁ := by
  induction e
  case intro h₁ h₂ _ hi => 
    constructor <;> intros
    · exact h₁ ‹_› |>.symm
    · exact h₂ ‹_› ‹_› |>.symm
    · exact hi ‹_› ‹_›

@[trans]
protected theorem trans (e₁ : rtr₁ ≈ rtr₂) (e₂ : rtr₂ ≈ rtr₃) : rtr₁ ≈ rtr₃ := by
  induction e₁ generalizing rtr₃; cases e₂
  case intro.intro h₁ h₂ _ hi h₁' h₂' h₃' => 
    constructor
    · intros; exact h₁ ‹_› |>.trans (h₁' ‹_›)
    · intro _ _ _ h _
      have ⟨_, h⟩ := Partial.mem_ids_iff.mp <| h₁ .rcn ▸ Partial.mem_ids_iff.mpr ⟨_, h⟩ 
      exact h₂ ‹_› h |>.trans (h₂' h ‹_›)
    · intro _ _ _ h _
      have ⟨_, h⟩ := Partial.mem_ids_iff.mp <| h₁ .rtr ▸ Partial.mem_ids_iff.mpr ⟨_, h⟩ 
      exact hi ‹_› h (h₃' h ‹_›)

theorem cmp?_ids_eq {cmp} : (rtr₁ ≈ rtr₂) → (cmp? cmp rtr₁).ids = (cmp? cmp rtr₂).ids 
  | intro h .. => h _

theorem rcns_some_eq : (rtr₁ ≈ rtr₂) → (rcns rtr₁ i = some r₁) → (rcns rtr₂ i = some r₂) → r₁ = r₂
  | intro _ h .. => h

theorem nest_equiv : (rtr₁ ≈ rtr₂) → (nest rtr₁ i = some n₁) → (nest rtr₂ i = some n₂) → n₁ ≈ n₂
  | intro _ _ h => h

theorem mem_cmp?_ids_iff {cmp} (e : rtr₁ ≈ rtr₂) : 
    (i ∈ (cmp? cmp rtr₁).ids) ↔ (i ∈ (cmp? cmp rtr₂).ids) := by
  rw [cmp?_ids_eq e]

theorem rcns_eq (e : rtr₁ ≈ rtr₂) : rcns rtr₂ = rcns rtr₁ := by
  funext i
  by_cases h₁ : i ∈ (rcns rtr₁).ids 
  all_goals have h₂ := cmp?_ids_eq e (cmp := .rcn) ▸ h₁
  case pos =>
    have ⟨_, h₁⟩ := Partial.mem_ids_iff.mp h₁
    have ⟨_, h₂⟩ := Partial.mem_ids_iff.mp h₂
    exact rcns_some_eq e h₁ h₂ ▸ h₁ |>.symm ▸ h₂
  case neg =>
    have h₁ := Partial.mem_ids_iff.not.mp h₁
    have h₂ := Partial.mem_ids_iff.not.mp h₂
    simp [cmp?] at h₁ h₂ 
    simp [Option.eq_none_iff_forall_not_mem.mpr h₁, Option.eq_none_iff_forall_not_mem.mpr h₂]

theorem cmp?_some_iff {cmp i} (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, cmp? cmp rtr₁ i = some o₁) ↔ (∃ o₂, cmp? cmp rtr₂ i = some o₂) := by
  simp [←Partial.mem_ids_iff, mem_cmp?_ids_iff e]

end Equivalent

theorem LawfulMemUpdate.equiv [ReactorType.WellFounded α] {rtr₁ : α} {cmp f} 
    (u : LawfulMemUpdate cmp i f rtr₁ rtr₂) : rtr₁ ≈ rtr₂ := by
  induction u <;> constructor
  case final.cmp?_ids_eq e h₁ h₂ =>
    intro c
    ext j
    by_cases hc : c = cmp <;> try subst hc
    case neg => exact e.mem_ids_iff (.inl hc)
    case pos =>
      by_cases hj : j = i <;> try subst hj
      case neg => exact e.mem_ids_iff (.inr hj)
      case pos => simp [Partial.mem_ids_iff, h₁, h₂]
  case final.rcns_some_eq e _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rcn) (j := j) (.inl $ by simp)
    simp_all [cmp?]
  case final.nest_equiv e _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rtr) (j := j) (.inl $ by simp)
    simp_all [cmp?]
    exact .refl
  case nest.cmp?_ids_eq j _ _ _ _ e h₁ h₂ _ _ =>
    intro c
    ext j'
    by_cases hc : c = .rtr <;> try subst hc
    case neg => exact e.mem_ids_iff (.inl hc)
    case pos => 
      by_cases hj : j' = j <;> try subst hj
      case neg => exact e.mem_ids_iff (.inr hj)
      case pos => simp [Partial.mem_ids_iff, h₁, h₂]
  case nest.rcns_some_eq e h₁ h₂ _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rcn) (j := j) (.inl $ by simp)
    simp_all [cmp?]
  case nest.nest_equiv j _ _ _ _ e _ _ _ hi =>
    intro j' n₁' n₂' h₁' h₂'
    by_cases hj : j' = j <;> try subst hj
    case pos => simp_all [cmp?]; assumption
    case neg => 
      have := e (c := .rtr) (j := j') (.inr hj)
      simp_all [cmp?]
      exact .refl

theorem LawfulUpdate.equiv [ReactorType.WellFounded α] {rtr₁ : α} {cmp f} :
    (LawfulUpdate cmp i f rtr₁ rtr₂) → rtr₁ ≈ rtr₂
  | notMem .. => .refl
  | update u  => u.equiv

theorem LawfulUpdatable.equiv [LawfulUpdatable α] {rtr : α} {cmp f} : 
    (Updatable.update rtr cmp i f) ≈ rtr := 
  Equivalent.symm (lawful rtr cmp i f).equiv

end ReactorType