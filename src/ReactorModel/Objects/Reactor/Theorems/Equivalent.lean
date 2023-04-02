import ReactorModel.Objects.Reactor.Theorems.LawfulCoe

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

variable [Indexable α] {rtr₁ : α}

theorem obj?_rcn_eq (e : rtr₁ ≈ rtr₂) : rtr₁[.rcn] = rtr₂[.rcn] :=
  sorry

theorem mem_iff {i} (e : rtr₁ ≈ rtr₂) : (i ∈ rtr₁[cpt]) ↔ (i ∈ rtr₂[cpt]) := by
  sorry

theorem obj?_rtr_equiv (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][i] = some n₁) (h₂ : rtr₂[.rtr][i] = some n₂) : 
    n₁ ≈ n₂ := by
  sorry

theorem obj?_some_iff (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, rtr₁[cpt][i] = some o₁) ↔ (∃ o₂, rtr₂[cpt][i] = some o₂) := 
  sorry

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

inductive Equivalent [ReactorType α] [ReactorType β] : 
    {rtr₁ : α} → {rtr₂ : β} → (Member cpt i rtr₁) → (Member cpt i rtr₂) → Prop 
  | final : Equivalent (.final h₁) (.final h₂)
  | nest {n₁ : α} {n₂ : β} {m₁ : Member cpt i n₁} {m₂ : Member cpt i n₂} :
    (h₁ : ReactorType.nest rtr₁ j = some n₁) → (h₂ : ReactorType.nest rtr₂ j = some n₂) → 
    (Equivalent m₁ m₂) → Equivalent (.nest h₁ m₁) (.nest h₂ m₂)

namespace Equivalent

@[refl]
theorem refl [ReactorType.WellFounded α] {rtr : α} {m : Member cpt i rtr} : 
    Equivalent m m := by
  induction rtr using ReactorType.WellFounded.induction
  case nest hi =>
    cases m
    case final  => exact .final
    case nest h => exact .nest _ _ (hi _ ⟨_, h⟩)

variable [ReactorType α] [ReactorType β]

theorem symm {rtr₁ : α} {rtr₂ : β} {m₁ : Member cpt i rtr₁} {m₂ : Member cpt i rtr₂}
    (e : Equivalent m₁ m₂) : (Equivalent m₂ m₁) := by
  induction e <;> constructor; assumption

theorem trans 
    [ReactorType γ] {rtr₁ : α} {rtr₂ : β} {rtr₃ : γ}
    {m₁ : Member cpt i rtr₁} {m₂ : Member cpt i rtr₂} {m₃ : Member cpt i rtr₃}
    (e₁ : Equivalent m₁ m₂) (e₂ : Equivalent m₂ m₃) : (Equivalent m₁ m₃) := by
  induction e₁ generalizing m₃ rtr₃ <;> cases e₂ <;> constructor
  case nest.nest hi₁ _ _ _ _ hi₂ => exact hi₁ hi₂

-- Lemma for `to_eq`.
private theorem to_eq' {rtr₁ rtr₂ : α} {m₁ : Member cpt i rtr₁} {m₂ : Member cpt i rtr₂} 
    (h : rtr₁ = rtr₂) (e : Equivalent m₁ m₂) : m₁ = cast (by simp [h]) m₂ := by
  induction e <;> subst h
  case final => rfl
  case nest m₁ _ h₁ _ hi h₂ => 
    injection h₁ ▸ h₂ with h
    simp [hi h, h]

theorem to_eq {rtr : α} {m₁ m₂ : Member cpt i rtr} (e : Equivalent m₁ m₂) : m₁ = m₂ := 
  e.to_eq' rfl

theorem from_lawfulCoe [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} 
    (m : Member cpt i rtr) : Equivalent m (m : Member cpt i (rtr : β)) := by
  induction m
  case final => constructor
  case nest e => simp [fromLawfulCoe, Equivalent.nest _ _ e]

end Equivalent

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

theorem UniqueIDs.lift [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} 
    (h : UniqueIDs (rtr : β)) : UniqueIDs rtr where
  allEq m₁ m₂ :=
    h.allEq (.fromLawfulCoe m₁) (.fromLawfulCoe m₂) ▸ Member.Equivalent.from_lawfulCoe m₁ 
      |>.trans (Member.Equivalent.from_lawfulCoe m₂).symm 
      |>.to_eq

instance [LawfulUpdatable α] [ind : Indexable β] [LawfulCoe α β] : Indexable α where
  unique_ids := UniqueIDs.lift ind.unique_ids 

open Equivalent
variable [Indexable α] [Indexable β] {rtr rtr₁ : α}

namespace Dependency
 
theorem equiv (e : rtr₁ ≈ rtr₂) (d : j₁ <[rtr₂] j₂) : j₁ <[rtr₁] j₂ := by
  induction d with
  | prio h₁ h₂ h₃ => 
    -- TODO: The next 2 lines are a common pattern in the `updated` proofs. Perhaps create a 
    --       (unidirectional) derivative of `Equivalent.obj?_some_iff` that includes equivalence.
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    exact prio h₁' (rcns_eq e ▸ h₂) (rcns_eq e ▸ h₃) ‹_› ‹_›
  | mutNorm h₁ h₂ h₃ => 
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩  
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    exact mutNorm h₁' (rcns_eq e ▸ h₂) (rcns_eq e ▸ h₃) ‹_› ‹_›
  | depOverlap h₁ h₂ => 
    exact depOverlap (e.obj?_rcn_eq.symm ▸ h₁) (e.obj?_rcn_eq.symm ▸ h₂) ‹_› ‹_› ‹_›
  | mutNest h₁ h₂ h₃ _ h₄ => 
    have ⟨_, h₁'⟩ := e.obj?_some_iff.mpr ⟨_, h₁⟩  
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    have ⟨_, h₂'⟩ := cpt?_some_iff e (cpt := .rtr) |>.mpr ⟨_, h₂⟩
    have h₄' := mem_cpt?_iff (Equivalent.nest_equiv e h₂' h₂) (cpt := .rcn) |>.mpr h₄
    exact mutNest h₁' h₂' (rcns_eq e ▸ h₃) ‹_› h₄'
  | trans _ _ d₁ d₂ => 
    exact trans d₁ d₂

theorem Acyclic.equiv (e : rtr₁ ≈ rtr₂) (a : Acyclic rtr₁) : Acyclic rtr₂ :=
  fun i d => absurd (d.equiv e) (a i) 

end Dependency

namespace Wellformed

set_option hygiene false in
scoped macro "equiv_nested_proof " name:ident : term => `(
  fun hc hp => 
    have e := Equivalent.obj?_rtr_equiv ‹_› h₁ h₂
    have ⟨_, hc'⟩ := Equivalent.cpt?_some_iff e (cpt := .rtr) |>.mp ⟨_, hc⟩ 
    have e := Equivalent.nest_equiv e hc hc'
    $(Lean.mkIdentFrom name $ `ValidDependency ++ name.getId) hc' 
    (Equivalent.mem_cpt?_iff e (cpt := .prt _) |>.mp hp)
)

theorem ValidDependency.equiv 
    (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][j] = some con₁) (h₂ : rtr₂[.rtr][j] = some con₂) : 
    (ValidDependency con₁ rk dk d) → ValidDependency con₂ rk dk d
  | stv h           => stv $ mem_cpt?_iff (obj?_rtr_equiv e h₁ h₂) (cpt := .stv) |>.mp h
  | act h           => act $ mem_cpt?_iff (obj?_rtr_equiv e h₁ h₂) (cpt := .act) |>.mp h
  | prt h           => prt $ mem_cpt?_iff (obj?_rtr_equiv e h₁ h₂) (cpt := .prt _) |>.mp h
  | nestedIn hc hp  => (equiv_nested_proof nestedIn) hc hp
  | nestedOut hc hp => (equiv_nested_proof nestedOut) hc hp

set_option hygiene false in
scoped macro "equiv_prio_proof " name:ident rtr₁:ident rtr₂:ident : term => `(
  fun h₁ h₂ h₃ => 
    have ⟨_, h₁'⟩ := Equivalent.obj?_some_iff ‹$rtr₁ ≈ $rtr₂› |>.mpr ⟨_, h₁⟩ 
    have e := Equivalent.obj?_rtr_equiv ‹_› h₁' h₁
    $(Lean.mkIdentFrom name $ `Wellformed ++ name.getId) 
      ‹_› h₁' (Equivalent.rcns_eq e ▸ h₂) (Equivalent.rcns_eq e ▸ h₃)
)

theorem equiv (e : rtr₁ ≈ rtr₂) (wf : Wellformed rtr₁) : Wellformed rtr₂ where
  overlap_prio  := equiv_prio_proof overlap_prio rtr₁ rtr₂
  hazards_prio  := equiv_prio_proof hazards_prio rtr₁ rtr₂
  mutation_prio := equiv_prio_proof mutation_prio rtr₁ rtr₂
  acyclic_deps  := wf.acyclic_deps.equiv e
  unique_inputs h₁ h₂ := wf.unique_inputs (e.obj?_rcn_eq.symm ▸ h₁) (e.obj?_rcn_eq.symm ▸ h₂)
  valid_deps h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := Equivalent.obj?_some_iff e |>.mpr ⟨_, h₁⟩ 
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    have h₂' := Equivalent.rcns_eq e ▸ h₂
    wf.valid_deps h₁' h₂' h₃ |>.equiv ‹_› h₁' h₁
  
end Wellformed
end ReactorType
