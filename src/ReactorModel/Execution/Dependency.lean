import ReactorModel.Components

open Classical Port

inductive Dependency.Internal (σ : Reactor) : ID → ID → Prop
  | rcns :
    (σ.con? .rcn i₁ = σ.con? .rcn i₂) →
    (σ.obj? .rcn i₁ = some rcn₁) →
    (σ.obj? .rcn i₂ = some rcn₂) →
    (rcn₁.prio > rcn₂.prio) →
    Internal σ i₁ i₂
  | mutNorm :
    (σ.con? .rcn iₘ = σ.con? .rcn iₙ) →
    (σ.obj? .rcn iₘ = some m) →
    (σ.obj? .rcn iₙ = some n) →
    (m.isMut) → 
    (n.isNorm) → 
    Internal σ iₘ iₙ

inductive Dependency.External (σ : Reactor) : ID → ID → Prop
  | port {i₁ i₂ : ID} :
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

open Dependency in
inductive Dependency (σ : Reactor) : ID → ID → Prop
  | internal : Internal σ i₁ i₂ → Dependency σ i₁ i₂
  | external : External σ i₁ i₂ → Dependency σ i₁ i₂
  | trans : Dependency σ i₁ i₂ → Dependency σ i₂ i₃ → Dependency σ i₁ i₃

notation i₁:max " >[" σ "] " i₂:max => Dependency σ i₁ i₂

protected theorem Dependency.irreflexive : ¬(rcn >[σ] rcn) := by
  by_contra h
  cases h
  case internal h => 
    cases h
    case rcns h₁ h₂ hp =>
      rw [Option.some_inj.mp $ h₁.symm.trans h₂] at hp
      sorry -- contradiction should work here, but doesn't ¯\_(ツ)_/¯  
    case mutNorm hrm hrn hm hn =>
      rw [Option.some_inj.mp $ hrm.symm.trans hrn, Reaction.isMut] at hm
      contradiction
  case external h =>
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
      let l₁ := Reactor.Lineage.rcn $ Finmap.ids_def'.mpr ⟨_, hm₁.symm⟩
      let l₂ := Reactor.Lineage.nest (.rcn hr) (Finmap.values_def.mp hn).choose_spec
      have := rtr₁.obj.uniqueIDs l₁ l₂
      contradiction
  case trans h₁ h₂ => 
    sorry -- either this should work by induction, or it's going to be a brutal cases h₁ <;> cases h₂

def Reactor.dependencies (σ : Reactor) (rcn : ID) : Set ID := { rcn' | rcn' >[σ] rcn }

def Indep (σ : Reactor) (rcn₁ rcn₂ : ID) : Prop :=
  ¬(rcn₁ >[σ] rcn₂) ∧ ¬(rcn₂ >[σ] rcn₁)

notation i₁:max " >[" σ "]< " i₂:max => Indep σ i₁ i₂

namespace Indep

protected theorem symm : (rcn₁ >[σ]< rcn₂) → (rcn₂ >[σ]< rcn₁) :=
  And.symm

protected theorem refl : rcn >[σ]< rcn := by
  simp [Indep, Dependency.irreflexive]

-- TODO: Since ne_rcns is false, make the outcome of the theorem:
--       (1.deps ∩ 2.deps = ∅) ∨ (1 = 2)

theorem ne_rtr_or_ne_out_deps : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (σ.con? .rcn i₁ ≠ σ.con? .rcn i₂) ∨ (rcn₁.deps .out ∩ rcn₂.deps .out) = ∅ := by
  intro h h₁ h₂ 
  by_contra hc
  have ⟨hc, hd⟩ := (not_or ..).mp hc
  simp at hc
  have ⟨rtr₁, hc₁, hr₁⟩ := Reactor.obj?_to_con?_and_cmp? h₁
  have ⟨rtr₂, hc₂, hr₂⟩ := Reactor.obj?_to_con?_and_cmp? h₂
  have H : rtr₁ = rtr₂ := sorry -- consequence of hc
  rw [←H] at hr₂
  cases rtr₁.obj.rcnsTotalOrder (.output hr₁ hr₂ h.ne_rcns hd)
  case h.inl hp => exact absurd (.internal $ .rcns hc.symm h₂ h₁ hp) h.right
  case h.inr hp => exact absurd (.internal $ .rcns hc      h₁ h₂ hp) h.left  

theorem ne_out_deps :
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (rcn₁.deps .out ∩ rcn₂.deps .out) = ∅ := by
  sorry -- Corollary of ne_rtr_or_ne_out_deps

theorem no_chain : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (rcn₁.deps .out ∩ rcn₂.deps Role.in) = ∅ :=
  sorry

theorem ne_rtr_or_pure : 
  (i₁ >[σ]< i₂) → (σ.obj? .rcn i₁ = some rcn₁) → (σ.obj? .rcn i₂ = some rcn₂) →
  (σ.con? .rcn i₁ ≠ σ.con? .rcn i₂) ∨ rcn₁.isPure ∨ rcn₂.isPure := by
  intro h h₁ h₂ 
  by_contra hc
  have ⟨hc, hd⟩ := (not_or ..).mp hc
  simp [not_or] at hd hc
  have ⟨rtr₁, hc₁, hr₁⟩ := Reactor.obj?_to_con?_and_cmp? h₁
  have ⟨rtr₂, hc₂, hr₂⟩ := Reactor.obj?_to_con?_and_cmp? h₂
  have H : rtr₁ = rtr₂ := sorry -- consequence of hc
  rw [←H] at hr₂
  cases rtr₁.obj.rcnsTotalOrder (.impure hr₁ hr₂ h.ne_rcns hd.left hd.right)
  case h.inl hp => exact absurd (.internal $ .rcns hc.symm h₂ h₁ hp) h.right
  case h.inr hp => exact absurd (.internal $ .rcns hc      h₁ h₂ hp) h.left  

end Indep