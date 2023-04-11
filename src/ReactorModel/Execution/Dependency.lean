import ReactorModel.Objects

namespace ReactorType

-- About the `↔`-condition in `prio`:  We want to establish a dependency between mutations with 
-- priorities as well normal reactions with priorities, but not between normal reactions and
-- mutations. Otherwise a normal reaction might take precedence over a mutation. Also the precedence
-- of mutations over normal reactions is handled by `mutNorm`, so this would potentially create a
-- redundancy.
--
-- Note: `Dependency rtr i₁ i₂` means that in `i₁` must occur before `i₂`. 
inductive Dependency [Indexable α] (rtr : α) : ID → ID → Prop
  | prio : 
    (rtr[.rtr][i] = some con) → (con{.rcn}{i₁} = some rcn₁) → (con{.rcn}{i₂} = some rcn₂) → 
    (rcn₁.Mutates ↔ rcn₂.Mutates) → (rcn₁.prio > rcn₂.prio) → Dependency rtr i₁ i₂
  | depOverlap {d : Reaction.Dependency} :
    (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (d ∈ rcn₁.deps .out) → 
    (d ∈ rcn₂.deps .in) → (d.cpt ≠ .stv) → Dependency rtr i₁ i₂
  | mutNorm : 
    (rtr[.rtr][i] = some con) → (con{.rcn}{iₘ} = some m) → (con{.rcn}{iₙ} = some n) → (m.Mutates) → 
    (n.Normal) → Dependency rtr iₘ iₙ
  | mutNest :
    (rtr[.rtr][i] = some rtr₁) → (rtr₁{.rtr}{j} = some rtr₂) → (rtr₁{.rcn}{iₘ} = some m) → 
    (m.Mutates) → (iᵣ ∈ rtr₂{.rcn}) → Dependency rtr iₘ iᵣ
  | trans : 
    Dependency rtr i₁ i₂ → Dependency rtr i₂ i₃ → Dependency rtr i₁ i₃

notation i₁ " <[" rtr "] " i₂ => Dependency rtr i₁ i₂

namespace Dependency

open Indexable Equivalent
variable [Indexable α] {rtr₁ : α}
 
theorem equiv (e : rtr₁ ≈ rtr₂) (d : j₁ <[rtr₂] j₂) : j₁ <[rtr₁] j₂ := by
  induction d with
  | prio h₁ h₂ h₃ => 
    -- TODO: The next 2 lines are a common pattern (see `Wellformed.equiv`). Perhaps create a 
    --       (unidirectional) derivative of `Equivalent.obj?_some_iff` that includes equivalence.
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    exact prio h₁' (get?_rcn_eq e ▸ h₂) (get?_rcn_eq e ▸ h₃) ‹_› ‹_›
  | mutNorm h₁ h₂ h₃ => 
    have ⟨_, h₁'⟩ := obj?_some_iff e |>.mpr ⟨_, h₁⟩  
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    exact mutNorm h₁' (get?_rcn_eq e ▸ h₂) (get?_rcn_eq e ▸ h₃) ‹_› ‹_›
  | depOverlap h₁ h₂ => 
    exact depOverlap (e.obj?_rcn_eq.symm ▸ h₁) (e.obj?_rcn_eq.symm ▸ h₂) ‹_› ‹_› ‹_›
  | mutNest h₁ h₂ h₃ _ h₄ => 
    have ⟨_, h₁'⟩ := e.obj?_some_iff.mpr ⟨_, h₁⟩  
    have e := Equivalent.obj?_rtr_equiv e h₁' h₁
    have ⟨_, h₂'⟩ := get?_some_iff e (cpt := .rtr) |>.mpr ⟨_, h₂⟩
    have h₄' := mem_get?_iff (Equivalent.get?_rtr_some_equiv e h₂' h₂) (cpt := .rcn) |>.mpr h₄
    exact mutNest h₁' h₂' (get?_rcn_eq e ▸ h₃) ‹_› h₄'
  | trans _ _ d₁ d₂ => 
    exact trans d₁ d₂

def Acyclic (rtr : α) : Prop :=
  ∀ i, ¬(i <[rtr] i)

theorem Acyclic.equiv (e : rtr₁ ≈ rtr₂) (a : Acyclic rtr₁) : Acyclic rtr₂ :=
  (a · $ ·.equiv e)

end Dependency
end ReactorType