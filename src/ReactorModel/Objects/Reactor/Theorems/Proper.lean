import ReactorModel.Objects.Reactor.Proper
import ReactorModel.Objects.Reactor.Theorems.Basic
import ReactorModel.Objects.Reactor.Theorems.Accessible
import ReactorModel.Objects.Reactor.Theorems.Readable

namespace ReactorType

instance [Proper α] : Readable α where
  ext_iff := Proper.toExtensional.ext_iff

instance [Proper α] : Accessible α where
  unique_ids := Proper.unique_ids
  wf         := Proper.wf

namespace Wellformed

open Indexable Equivalent
variable [Indexable α] {rtr rtr₁ : α}

scoped macro "equiv_local_proof " dep:ident : term => 
  `($dep $ mem_get?_iff (obj?_rtr_equiv ‹_› ‹_› ‹_›) |>.mp ‹_›)

set_option hygiene false in
scoped macro "equiv_nested_proof " dep:ident : term => `(
  fun hc hp => 
    have e        := obj?_rtr_equiv ‹_› h₁ h₂
    have ⟨_, hc'⟩ := get?_some_iff e |>.mp ⟨_, hc⟩ 
    $dep hc' $ (mem_get?_iff $ get?_rtr_some_equiv e hc hc').mp hp
)

theorem ValidDependency.equiv 
    (e : rtr₁ ≈ rtr₂) (h₁ : rtr₁[.rtr][j] = some con₁) (h₂ : rtr₂[.rtr][j] = some con₂) : 
    (ValidDependency con₁ rk dk d) → ValidDependency con₂ rk dk d
  | inp h           => equiv_local_proof inp
  | out h           => equiv_local_proof out
  | stv h           => equiv_local_proof stv
  | act h           => equiv_local_proof act
  | nestedIn  hc hp => (equiv_nested_proof nestedIn) hc hp
  | nestedOut hc hp => (equiv_nested_proof nestedOut) hc hp

theorem equiv (e : rtr₁ ≈ rtr₂) (wf : Wellformed rtr₁) : Wellformed rtr₂ where
  unique_inputs h₁ h₂ := 
    wf.unique_inputs (e.obj?_rcn_eq.symm ▸ h₁) (e.obj?_rcn_eq.symm ▸ h₂)
  ordered_prio h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩ 
    have e := obj?_rtr_equiv ‹_› h₁' h₁
    ordered_prio ‹_› h₁' (get?_rcn_eq e ▸ h₂) (get?_rcn_eq e ▸ h₃)
  valid_deps h₁ h₂ h₃ := 
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩ 
    have e := obj?_rtr_equiv ‹_› h₁' h₁
    wf.valid_deps h₁' (get?_rcn_eq e ▸ h₂) h₃ |>.equiv ‹_› h₁' h₁

theorem nested (wf : Wellformed rtr₁) (h : rtr₁{.rtr}{i} = some rtr₂) : Wellformed rtr₂ where
  unique_inputs h₁ h₂ := wf.unique_inputs (obj?_some_nested h h₁) (obj?_some_nested h h₂)
  ordered_prio h₁     := wf.ordered_prio (obj?_some_nested' h h₁).choose_spec
  valid_deps h₁       := wf.valid_deps (obj?_some_nested' h h₁).choose_spec
  
variable (wf : Wellformed rtr)

theorem shared_dep_local 
    (hc₁ : rtr[.rtr][c₁] = some con₁) (hc₂ : rtr[.rtr][c₂] = some con₂)
    (hr₁ : con₁{.rcn}{i₁} = some rcn₁) (hr₂ : con₂{.rcn}{i₂} = some rcn₂)
    (hd₁ : ⟨cpt, j⟩ ∈ rcn₁.deps k) (hd₂ : ⟨cpt, j⟩ ∈ rcn₂.deps k) : 
    c₁ = c₂ := by
  by_cases hi : i₁ = i₂
  case pos => exact get?_some_rtr_eq hc₁ hc₂ (hi ▸ hr₁) hr₂
  case neg =>
    have hv₁ := wf.valid_deps hc₁ hr₁ hd₁
    have hv₂ := wf.valid_deps hc₂ hr₂ hd₂
    cases k <;> cases cpt <;> try cases ‹Kind› 
    have := obj?_some_extend hc₁ hr₁
    case out.inp => 
      have hd₂' := wf.unique_inputs (obj?_some_extend hc₁ hr₁) (obj?_some_extend hc₂ hr₂) hi hd₁
      exact absurd hd₂ hd₂'
    case in.out =>
      cases hk₁ : rcn₁.kind <;> cases hk₂ : rcn₂.kind <;> cases hk₁ ▸ hv₁ <;> cases hk₂ ▸ hv₂
      case _ hn₁ hj₁ _ _ hn₂ hj₂ =>
        have hc₁' := obj?_some_extend hc₁ hn₁
        have hc₂' := obj?_some_extend hc₂ hn₂
        have hj := mem_get?_rtr_eq hc₁' hc₂' hj₁ hj₂
        injection hj with hj
        exact get?_some_rtr_eq hc₁ hc₂ (hj ▸ hn₁) hn₂ 
    all_goals 
      cases hk₁ : rcn₁.kind <;> cases hk₂ : rcn₂.kind <;> cases hk₁ ▸ hv₁ <;> cases hk₂ ▸ hv₂
      all_goals exact mem_get?_rtr_eq hc₁ hc₂ ‹_› ‹_› 
        
theorem shared_state_local
    (hc₁ : rtr[.rtr][c₁] = some con₁) (hc₂ : rtr[.rtr][c₂] = some con₂)
    (hr₁ : con₁{.rcn}{i₁} = some rcn₁) (hr₂ : con₂{.rcn}{i₂} = some rcn₂) 
    (hd₁ : ⟨.stv, j⟩ ∈ rcn₁.deps k₁) (hd₂ : ⟨.stv, j⟩ ∈ rcn₂.deps k₂) : 
    c₁ = c₂ := by
  have hv₁ := wf.valid_deps hc₁ hr₁ hd₁
  have hv₂ := wf.valid_deps hc₂ hr₂ hd₂
  cases hk₁ : rcn₁.kind <;> cases hk₂ : rcn₂.kind <;> cases hk₁ ▸ hv₁ <;> cases hk₂ ▸ hv₂
  all_goals exact mem_get?_rtr_eq hc₁ hc₂ ‹_› ‹_› 

end Wellformed

open Indexable in
theorem Proper.ext_obj? [Proper α] {rtr₁ : α} (e : rtr₁ ≈ rtr₂) 
    (h : ∀ {c i o₁ o₂}, (c ≠ .rtr) → (rtr₁[c][i] = some o₁) → (rtr₂[c][i] = some o₂) → o₁ = o₂) : 
    rtr₁ = rtr₂ := by
  induction rtr₁ using WellFounded.induction generalizing rtr₂
  case nested rtr₁ hi =>
    ext1; funext cpt i
    case _ =>
      cases hc₁ : rtr₁{cpt}{i}
      case none => simp [Equivalent.get?_none_iff e |>.mp hc₁]
      case some n₁ =>
        have ⟨n₂, hc₂⟩ := Equivalent.get?_some_iff e |>.mp ⟨_, hc₁⟩ 
        simp [hc₂]
        cases cpt
        case rtr =>
          apply hi n₁ ⟨_, hc₁⟩ $ Equivalent.get?_rtr_some_equiv e hc₁ hc₂
          intro c _ _ _ hn ho₁ ho₂
          cases c <;> try contradiction
          all_goals exact h hn (obj?_some_nested hc₁ ho₁) (obj?_some_nested hc₂ ho₂)
        all_goals 
          have ho₁ := get?_some_to_obj?_some hc₁
          have ho₂ := get?_some_to_obj?_some hc₂
          exact h (by simp) ho₁ ho₂
        
theorem LawfulUpdate.ne_comm [Proper α] {rtr rtr₁ rtr₁' rtr₂ rtr₂' : α} 
    (u₁ : LawfulUpdate cpt₁ i₁ f₁ rtr rtr₁) (u₂ : LawfulUpdate cpt₂ i₂ f₂ rtr₁ rtr₂) 
    (u₁' : LawfulUpdate cpt₂ i₂ f₂ rtr rtr₁') (u₂' : LawfulUpdate cpt₁ i₁ f₁ rtr₁' rtr₂') 
    (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂) : rtr₂ = rtr₂' := by
  have e₁ := Equivalent.trans u₁.equiv u₂.equiv
  have e₂ := Equivalent.trans u₁'.equiv u₂'.equiv
  have e := Equivalent.trans (Equivalent.symm e₁) e₂
  apply Proper.ext_obj? e
  intro cpt i _ _ hc ho₁ ho₂
  cases cpt
  case rtr => contradiction
  case rcn => simp_all [Equivalent.obj?_rcn_eq e]
  case val cpt _ _ =>
    -- TODO: Simplify this case bashing a bit when this is fixed:
    --       https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/by_cases.20tags.20bug/near/345415921
    by_cases hc₁ : cpt = cpt₁ <;> by_cases hc₂ : cpt = cpt₂ <;> ((try subst hc₁); try subst hc₂)
    · by_cases hi₁ : i = i₁ <;> by_cases hi₂ : i = i₂ <;> ((try subst hi₁); try subst hi₂)
      · simp at h
      · have h₁ := u₁.obj?_updated ▸ u₂.obj?_preserved (.inr hi₂) 
        have h₂ := u₁'.obj?_preserved (.inr hi₂) ▸ u₂'.obj?_updated  
        injection ho₁ ▸ h₂.trans h₁.symm ▸ ho₂
      · have h₁ := u₁.obj?_preserved (.inr hi₁) ▸ u₂.obj?_updated
        have h₂ := u₁'.obj?_updated ▸ u₂'.obj?_preserved (.inr hi₁)
        injection ho₁ ▸ h₂.trans h₁.symm ▸ ho₂
      · have := u₁.obj?_preserved  (.inr hi₁) ▸ u₂.obj?_preserved  (.inr hi₂) 
        have := u₁'.obj?_preserved (.inr hi₂) ▸ u₂'.obj?_preserved (.inr hi₁)
        simp_all
    · by_cases hi₁ : i = i₁ <;> try subst hi₁
      · have h₁ := u₁.obj?_updated ▸ u₂.obj?_preserved (.inl hc₂) 
        have h₂ := u₁'.obj?_preserved (.inl hc₂) ▸ u₂'.obj?_updated  
        injection ho₁ ▸ h₂.trans h₁.symm ▸ ho₂
      · have := u₁.obj?_preserved  (.inr hi₁) ▸ u₂.obj?_preserved (.inl hc₂) 
        have := u₁'.obj?_preserved (.inl hc₂) ▸ u₂'.obj?_preserved (.inr hi₁)
        simp_all
    · by_cases hi₂ : i = i₂ <;> try subst hi₂
      · have h₁ := u₁.obj?_preserved (.inl hc₁) ▸ u₂.obj?_updated 
        have h₂ := u₁'.obj?_updated ▸ u₂'.obj?_preserved (.inl hc₁)  
        injection ho₁ ▸ h₂.trans h₁.symm ▸ ho₂
      · have := u₁.obj?_preserved  (.inl hc₁) ▸ u₂.obj?_preserved (.inr hi₂) 
        have := u₁'.obj?_preserved (.inr hi₂) ▸ u₂'.obj?_preserved (.inl hc₁)
        simp_all
    · have := u₁.obj?_preserved  (j := i) (.inl hc₁) ▸ u₂.obj?_preserved  (.inl hc₂) 
      have := u₁'.obj?_preserved (j := i) (.inl hc₂) ▸ u₂'.obj?_preserved (.inl hc₁)
      simp_all

open Updatable in
theorem LawfulUpdatable.update_ne_comm [Proper α] {rtr : α} (h : cpt₁ ≠ cpt₂ ∨ i₁ ≠ i₂):
    update (update rtr cpt₁ i₁ f₁) cpt₂ i₂ f₂ = update (update rtr cpt₂ i₂ f₂) cpt₁ i₁ f₁ :=
  LawfulUpdate.ne_comm (lawful ..) (lawful ..) (lawful ..) (lawful ..) h
  
end ReactorType