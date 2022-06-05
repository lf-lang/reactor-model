import ReactorModel.Components

open Classical Port

-- About the norm-condition in prio: 
-- We want to establish a dependency between mutations with priorities 
-- as well normal reactions with priorities, but not between normal reactions
-- and mutations. Otherwise a normal reaction might take precedence over
-- a mutation. Also the precedence of mutations over normal reactions is
-- handled by mutNorm - so this would potentially just create a redundancy.
inductive Dependency.Internal (σ : Reactor) : ID → ID → Prop
  | prio :
    (σ.con? .rcn i₁ = σ.con? .rcn i₂) →
    (σ.obj? .rcn i₁ = some rcn₁) →
    (σ.obj? .rcn i₂ = some rcn₂) →
    (rcn₁.isMut ↔ rcn₂.isMut) → 
    (rcn₁.prio > rcn₂.prio) →
    Internal σ i₁ i₂
  | mutNorm :
    (σ.con? .rcn iₘ = σ.con? .rcn iₙ) →
    (σ.obj? .rcn iₘ = some m) →
    (σ.obj? .rcn iₙ = some n) →
    (m.isMut) → 
    (n.isNorm) → 
    Internal σ iₘ iₙ

theorem Dependency.Internal.irreflexive : ¬(Dependency.Internal σ i i) := by
  intro h
  cases h
  case prio h₁ h₂ _ hp =>
    rw [Option.some_inj.mp $ h₁.symm.trans h₂] at hp
    -- TODO: This is probably related to `instance : PartialOrder Priority`.
    sorry -- contradiction should work on hp, but doesn't ¯\_(ツ)_/¯  
  case mutNorm hrm hrn hm hn =>
    rw [Option.some_inj.mp $ hrm.symm.trans hrn, Reaction.isMut] at hm
    contradiction

inductive Dependency.External (σ : Reactor) : ID → ID → Prop
  | port {i₁ i₂ : ID} : -- TODO: This also works for actions, doesn't
    (σ.obj? .rcn i₁ = some rcn₁) →
    (σ.obj? .rcn i₂ = some rcn₂) →
    ((rcn₁.deps .out ∩ rcn₂.deps .«in»).nonempty) →
    External σ i₁ i₂
  | «mut» {iₘ : ID} :
    (σ.obj? .rcn iₘ = some m) → 
    (m.isMut) → 
    (σ.con? .rcn iₘ = some rtr₁) →
    (rtr₂ ∈ rtr₁.obj.nest.values) → 
    (iᵣ ∈ rtr₂.rcns.ids) → 
    External σ iₘ iᵣ

theorem Dependency.External.irreflexive : ¬(Dependency.External σ i i) := by
  intro h
  cases h
  case port rcn _ hi h₁ h₂ =>
    simp [←Option.some_inj.mp $ h₁.symm.trans h₂, Finset.nonempty, Finset.mem_inter] at hi
    have ⟨p, ho, hi⟩ := hi
    simp
    by_cases hc : rcn.isNorm
    case pos => sorry -- Use Reactor.wfNormDeps
    case neg => sorry -- Use Reactor.wfMutDeps
  case «mut» rtr₁ _ _ hn _ hc hr =>
    have ⟨_, _, hm₁⟩ := Reactor.con?_to_obj?_and_cmp? hc
    let l₁ := Reactor.Lineage.end .rcn $ Finmap.ids_def'.mpr ⟨_, hm₁⟩
    let l₂ := Reactor.Lineage.nest (.end .rcn hr) (Finmap.values_def.mp hn).choose_spec
    have := rtr₁.obj.uniqueIDs l₁ l₂
    contradiction

open Dependency in
inductive Dependency (σ : Reactor) : ID → ID → Prop
  | internal : Internal σ i₁ i₂ → Dependency σ i₁ i₂
  | external : External σ i₁ i₂ → Dependency σ i₁ i₂
  | trans : Dependency σ i₁ i₂ → Dependency σ i₂ i₃ → Dependency σ i₁ i₃

notation i₁:max " >[" σ "] " i₂:max => Dependency σ i₁ i₂

-- WARNING: This is false for transitive port dependencies.
/-
protected theorem Dependency.irreflexive (he : rcn = rcn') : ¬(rcn >[σ] rcn') := by
  by_contra h
  induction h
  case' internal h, external h => simp [he] at h; exact h.irreflexive
  case trans rcn' h₁ h₂ _ _ => 
    simp [he] at h₁
    cases h₁ <;> cases h₂
    case internal.internal h₁ h₂ =>
      cases h₁ <;> cases h₂
      case prio.prio h₁ h₂ _ hp _ _ _ h₁' h₂' _ hp' =>
        rw [Option.some_inj.mp $ h₁.symm.trans h₂'] at hp
        rw [Option.some_inj.mp $ h₁'.symm.trans h₂] at hp'
        sorry -- contradiction should work on hp and hp', but doesn't ¯\_(ツ)_/¯ 
      case mutNorm.mutNorm h₁ h₂ hm _ _ _ _ h₁' h₂' _ hn =>
        rw [Option.some_inj.mp $ h₁.symm.trans h₂'] at hm
        contradiction
      case' prio.mutNorm h₁ h₂ he _ _ _ _ h₁' h₂' hm hn, mutNorm.prio h₁' h₂' hm hn _ _ _ h₁ h₂ he _ =>
        rw [Option.some_inj.mp $ h₁.symm.trans h₂'] at he
        rw [←Option.some_inj.mp $ h₁'.symm.trans h₂] at he
        exact absurd hn (he.mpr hm)
    case external.external h₁ h₂ =>
      cases h₁ <;> cases h₂ 
      case port.port =>
        sorry -- WARNING: This is case isn't provable.
      case mut.mut =>
        sorry -- contradiction: rcn contains rcn' and vice versa
      case' port.mut, mut.port =>
        sorry
    case' internal.external, external.internal =>
      sorry
    case internal.trans
-/

def Reactor.dependencies (σ : Reactor) (rcn : ID) : Set ID := { rcn' | rcn' >[σ] rcn }

def Indep (σ : Reactor) (rcn₁ rcn₂ : ID) : Prop :=
  ¬(rcn₁ >[σ] rcn₂) ∧ ¬(rcn₂ >[σ] rcn₁)

notation i₁:max " >[" σ "]< " i₂:max => Indep σ i₁ i₂

namespace Indep

protected theorem symm : (rcn₁ >[σ]< rcn₂) → (rcn₂ >[σ]< rcn₁) :=
  And.symm

-- TODO: Come up with better names for these theorems.

theorem nonoverlapping_deps : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (rcn₁.deps .out ∩ rcn₂.deps .«in») = ∅ := by
  intro ⟨hi, _⟩ ho₁ ho₂
  by_contra hc
  simp [Finset.eq_empty_iff_forall_not_mem] at hc
  exact absurd (Dependency.external $ .port ho₁ ho₂ hc) hi

theorem ne_rtr_or_pure : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (σ.con? .rcn i₁ = some c₁) → (σ.con? .rcn i₂ = some c₂) →
  (c₁.id ≠ c₂.id) ∨ rcn₁.isPure ∨ rcn₂.isPure := by
  intro h ho₁ ho₂ hc₁ hc₂ 
  by_contra hc
  have ⟨hc, hp⟩ := (not_or ..).mp hc
  simp [not_or] at hp hc
  -- have ⟨rtr₁, hc₁, hr₁⟩ := Reactor.obj?_to_con?_and_cmp? ho₁
  -- have ⟨rtr₂, hc₂, hr₂⟩ := Reactor.obj?_to_con?_and_cmp? ho₂
  -- rw [hc] at hc₁
  -- simp [Option.some_inj.mp $ hc₁.symm.trans hc₂, Reactor.cmp?] at hr₁ hr₂
  sorry
  /-cases rtr₂.obj.rcnsTotalOrder (.impure hr₁ hr₂ sorry hp.left hp.right)
  case h.inl hp => exact absurd (.internal $ .prio hc.symm h₂ h₁ hp) h.right
  case h.inr hp => exact absurd (.internal $ .rcns hc      h₁ h₂ hp) h.left  
  -/

end Indep