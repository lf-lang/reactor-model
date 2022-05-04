import ReactorModel.Components.Get

namespace Reactor

-- Two reactors are equivalent if they are structurally equal.
structure Equiv (σ₁ σ₂ : Reactor) : Prop where
  top : ∀ cmp, σ₁.ids cmp = σ₂.ids cmp
  nest : ∀ {i : ID} cmp, (σ₁.obj? .rtr i = some rtr₁) → (σ₂.obj? .rtr i = some rtr₂) → rtr₁.ids cmp = rtr₂.ids cmp

notation σ₁:max " ≈ " σ₂:max => Reactor.Equiv σ₁ σ₂

variable {σ σ₁ σ₂ σ₃ : Reactor}

theorem Equiv.nest' {i : ID} : 
  (σ₁ ≈ σ₂) → (σ₁.obj? .rtr i = some rtr₁) → (σ₂.obj? .rtr i = some rtr₂) → (rtr₁ ≈ rtr₂) := 
  λ he ho₁ ho₂ => {
    top := λ _ => he.nest _ ho₁ ho₂,
    nest := λ _ ho₁' ho₂' => he.nest _ (Reactor.obj?_sub ho₁ ho₁') (Reactor.obj?_sub ho₂ ho₂')
  }

theorem Equiv.obj?_iff {i : ID} : 
  (σ₁ ≈ σ₂) → ((∃ o₁, σ₁.obj? cmp i = some o₁) ↔ (∃ o₂, σ₂.obj? cmp i = some o₂)) := by 
  intro he
  constructor <;> (
    intro ho
    simp [←ids_mem_iff_obj?, ←he.top] at *
    exact ho
  )

@[simp]
theorem Equiv.refl : σ ≈ σ := {
  top := by simp,
  nest := λ _ h₁ h₂ => by rw [Option.some_inj.mp <| h₁.symm.trans h₂]
}

theorem Equiv.trans : (σ₁ ≈ σ₂) → (σ₂ ≈ σ₃) → (σ₁ ≈ σ₃) := by
  intro h₁₂ h₂₃
  constructor
  case top => 
    intro _
    exact (h₁₂.top _).trans (h₂₃.top _)
  case nest => 
    intro _ _ _ _ h₁ h₂
    have ⟨_, hm⟩ := h₁₂.obj?_iff.mp ⟨_, h₁⟩
    rw [h₁₂.nest _ h₁ hm, h₂₃.nest _ hm h₂]

theorem Equiv.eq_obj?_nest {i j : ID} :
  (σ₁ ≈ σ₂) → (σ₁.obj? cmp i = σ₂.obj? cmp i) → 
  (σ₁.obj? .rtr j = some rtr₁) → (σ₂.obj? .rtr j = some rtr₂) → 
  rtr₁.obj? cmp i = rtr₂.obj? cmp i := by
  intro he ho hr₁ hr₂ 
  have he' := he.nest' hr₁ hr₂
  sorry

end Reactor