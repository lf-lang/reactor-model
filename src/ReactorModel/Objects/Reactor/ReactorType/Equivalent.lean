import ReactorModel.Objects.Reactor.ReactorType.Updatable

noncomputable section
open Classical

namespace ReactorType 

inductive Equivalent [ReactorType α] : α → α → Prop
  | intro
    (mem_cpt?_iff : ∀ cpt j, (j ∈ cpt? cpt rtr₁) ↔ (j ∈ cpt? cpt rtr₂)) 
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
    · exact h₁ ‹_› ‹_› |>.symm
    · exact h₂ ‹_› ‹_› |>.symm
    · exact hi ‹_› ‹_›
 
@[trans]
protected theorem trans (e₁ : rtr₁ ≈ rtr₂) (e₂ : rtr₂ ≈ rtr₃) : rtr₁ ≈ rtr₃ := by
  induction e₁ generalizing rtr₃; cases e₂
  case intro.intro h₁ h₂ _ hi h₁' h₂' h₃' => 
    constructor
    · intros; exact h₁ ‹_› ‹_› |>.trans (h₁' ‹_› ‹_›)
    · intro _ _ _ h _
      have ⟨_, h⟩ := Partial.mem_iff.mp <| h₁ .rcn ‹_› |>.mp $ Partial.mem_iff.mpr ⟨_, h⟩
      exact h₂ ‹_› h |>.trans (h₂' h ‹_›)
    · intro _ _ _ h _
      have ⟨_, h⟩ := Partial.mem_iff.mp <| h₁ .rtr ‹_› |>.mp $ Partial.mem_iff.mpr ⟨_, h⟩ 
      exact hi ‹_› h (h₃' h ‹_›)

theorem mem_cpt?_iff : (rtr₁ ≈ rtr₂) → (i ∈ cpt? cpt rtr₁ ↔ i ∈ cpt? cpt rtr₂)
  | intro h .. => h _ _

theorem rcns_some_eq : (rtr₁ ≈ rtr₂) → (rcns rtr₁ i = some r₁) → (rcns rtr₂ i = some r₂) → r₁ = r₂
  | intro _ h .. => h

theorem nest_equiv : (rtr₁ ≈ rtr₂) → (nest rtr₁ i = some n₁) → (nest rtr₂ i = some n₂) → n₁ ≈ n₂
  | intro _ _ h => h

theorem rcns_eq (e : rtr₁ ≈ rtr₂) : rcns rtr₂ = rcns rtr₁ := by
  funext i
  by_cases h₁ : i ∈ rcns rtr₁ 
  case pos =>
    have ⟨_, h₂⟩ := Partial.mem_iff.mp $ mem_cpt?_iff e (cpt := .rcn) |>.mp h₁
    have ⟨_, h₁⟩ := Partial.mem_iff.mp h₁
    exact rcns_some_eq e h₁ h₂ ▸ h₁ |>.symm ▸ h₂
  case neg =>
    have h₂ := Partial.mem_iff.not.mp $ mem_cpt?_iff e (cpt := .rcn) |>.not.mp h₁
    have h₁ := Partial.mem_iff.not.mp h₁
    simp [cpt?] at h₁ h₂ 
    simp [Option.eq_none_iff_forall_not_mem.mpr h₁, Option.eq_none_iff_forall_not_mem.mpr h₂]

theorem cpt?_some_iff (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, cpt? cpt rtr₁ i = some o₁) ↔ (∃ o₂, cpt? cpt rtr₂ i = some o₂) := by
  simp [←Partial.mem_iff, mem_cpt?_iff e]

end Equivalent

theorem LawfulMemUpdate.equiv [ReactorType.WellFounded α] {rtr₁ : α}
    (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) : rtr₁ ≈ rtr₂ := by
  induction u <;> constructor
  case final.mem_cpt?_iff e h₁ h₂ =>
    intro c j
    by_cases hc : c = cpt <;> try subst hc
    case neg => exact e.mem_iff (.inl hc)
    case pos =>
      by_cases hj : j = i <;> try subst hj
      case neg => exact e.mem_iff (.inr hj)
      case pos => simp [Partial.mem_iff, h₁, h₂]
  case final.rcns_some_eq e _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rcn) (j := j) (.inl $ by simp)
    simp_all [cpt?]
  case final.nest_equiv e _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rtr) (j := j) (.inl $ by simp)
    simp_all [cpt?]
    exact .refl
  case nest.mem_cpt?_iff j _ _ _ _ e h₁ h₂ _ _ =>
    intro c j'
    by_cases hc : c = .rtr <;> try subst hc
    case neg => exact e.mem_iff (.inl hc)
    case pos => 
      by_cases hj : j' = j <;> try subst hj
      case neg => exact e.mem_iff (.inr hj)
      case pos => simp [Partial.mem_iff, h₁, h₂]
  case nest.rcns_some_eq e h₁ h₂ _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rcn) (j := j) (.inl $ by simp)
    simp_all [cpt?]
  case nest.nest_equiv j _ _ _ _ e _ _ _ hi =>
    intro j' n₁' n₂' h₁' h₂'
    by_cases hj : j' = j <;> try subst hj
    case pos => simp_all [cpt?]; assumption
    case neg => 
      have := e (c := .rtr) (j := j') (.inr hj)
      simp_all [cpt?]
      exact .refl

theorem LawfulUpdate.equiv [ReactorType.WellFounded α] {rtr₁ : α} :
    (LawfulUpdate cpt i f rtr₁ rtr₂) → rtr₁ ≈ rtr₂
  | notMem _ h => h ▸ .refl
  | update u   => u.equiv

theorem LawfulUpdatable.equiv [LawfulUpdatable α] {rtr : α} : 
    (Updatable.update rtr cpt i f) ≈ rtr := 
  Equivalent.symm (lawful rtr cpt i f).equiv

namespace Member

variable [ReactorType.WellFounded α] {rtr₁ : α}

def fromLawfulMemUpdate {rtr₁ : α} : 
    (Member c j rtr₂) → (LawfulMemUpdate cpt i f rtr₁ rtr₂) → Member c j rtr₁
  | final h, u => final (Equivalent.mem_cpt?_iff u.equiv |>.mpr h)
  | nest h m (j := j), .final e _ _ => 
    nest (m := m) $ by 
      have h' := e (c := .rtr) (j := j) (.inl $ by simp)
      simp [cpt?] at h'
      exact h'.symm ▸ h
  | nest h m (j := j₂), .nest e h₁ h₂ u (j := j₁) =>
      if hj : j₂ = j₁ then
        let m' := (hj ▸ h |>.symm.trans h₂ |> Option.some_inj.mp) ▸ m 
        nest h₁ $ fromLawfulMemUpdate m' u
      else
        nest (m := m) $ by 
          have h' := e (c := .rtr) (.inr hj)
          simp [cpt?] at h'
          exact h'.symm ▸ h

def fromLawfulUpdate (m : Member c j rtr₂) : (LawfulUpdate cpt i f rtr₁ rtr₂) → Member c j rtr₁
  | .notMem _ h => h ▸ m
  | .update u   => m.fromLawfulMemUpdate u

theorem Equivalent.from_lawfulMemUpdate (u : LawfulMemUpdate cpt i f rtr₁ rtr₂) 
    (m : Member c j rtr₂) : Equivalent m (m.fromLawfulMemUpdate u) := by
  induction u <;> cases m <;> (simp [fromLawfulMemUpdate]; try exact .final)
  case final.nest e _ _ j _ _ hn => 
    have h := e (c := .rtr) (j := j) (.inl $ by simp)
    simp [cpt?] at h
    exact .nest hn (h ▸ hn) .refl
  case nest.nest e h₁ h₂ _ hi _ _ m hn =>
    split
    case inl hj =>
      subst hj
      cases Option.some_inj.mp $ hn.symm.trans h₂
      exact .nest hn h₁ (hi m)
    case inr hj =>
      have h := e (c := .rtr) (.inr hj)
      simp [cpt?] at h
      exact .nest hn (h.symm ▸ hn) .refl

theorem Equivalent.from_lawfulUpdate (u : LawfulUpdate cpt i f rtr₁ rtr₂) 
    (m : Member c j rtr₂) : Equivalent m (m.fromLawfulUpdate u) := by
  cases u
  case notMem _ h => cases h; rfl
  case update u   => exact Equivalent.from_lawfulMemUpdate u m 
    
end Member
end ReactorType