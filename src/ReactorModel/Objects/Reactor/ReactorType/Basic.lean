import ReactorModel.Objects.Reaction

open Reactor (Component)

class ReactorType (α : Type) where
  ports : α → Kind → ID ⇀ Value             
  acts  : α → ID ⇀ Action
  state : α → ID ⇀ Value            
  rcns  : α → ID ⇀ Reaction         
  nest  : α → ID ⇀ α      
 
namespace ReactorType

scoped macro "lawfulCoe_nest_proof" : tactic => 
  `(tactic| simp [ReactorType.nest, Partial.map_map, Function.comp, Partial.attach_map_val])

scoped macro "lawfulCoe_inj_proof" : tactic => 
  `(tactic| (simp [Function.Injective]; intro ⟨_, _⟩ ⟨_, _⟩; simp))

class LawfulCoe (α β) [a : ReactorType α] [b : ReactorType β] extends Coe α β where
  ports : b.ports ∘ coe = a.ports                    := by rfl
  acts  : b.acts  ∘ coe = a.acts                     := by rfl
  rcns  : b.rcns  ∘ coe = a.rcns                     := by rfl
  state : b.state ∘ coe = a.state                    := by rfl
  nest  : b.nest  ∘ coe = (Partial.map coe) ∘ a.nest := by lawfulCoe_nest_proof
  inj   : coe.Injective                              := by lawfulCoe_inj_proof

theorem LawfulCoe.nest' [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] :
    b.nest (c.coe rtr) = (a.nest rtr).map c.coe := by
  rw [←Function.comp_apply (f := ReactorType.nest), c.nest]
  simp

theorem LawfulCoe.coe_ext_iff [ReactorType α] [ReactorType β] [c : LawfulCoe α β] 
    {rtr₁ rtr₂ : α} : rtr₁ = rtr₂ ↔ (rtr₁ : β) = (rtr₂ : β) :=
  ⟨(congr_arg _ ·), (c.inj ·)⟩

abbrev componentType [ReactorType α] : Component → Type
  | .rtr     => α 
  | .rcn     => Reaction
  | .val cpt => cpt.type

abbrev cpt? [inst : ReactorType α] : (cpt : Component) → α → ID ⇀ inst.componentType cpt
  | .rtr   => nest 
  | .rcn   => rcns
  | .prt k => (ports · k)
  | .act   => acts
  | .stv   => state

namespace LawfulCoe

variable [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] {rtr : α}

instance : Coe (a.componentType cpt) (b.componentType cpt) where
  coe := 
    match cpt with
    | .rcn | .prt _ | .act | .stv => id
    | .rtr => c.coe

theorem lower_cpt?_eq_some (cpt) {o} (h : a.cpt? cpt rtr i = some o) : 
    b.cpt? cpt rtr i = some ↑o := by
  split <;> simp_all [cpt?, ←c.rcns, ←c.ports, ←c.acts, ←c.state]
  simp [c.nest', Partial.map_val]
  exists o

theorem lower_mem_cpt?_ids (cpt) (h : i ∈ (cpt? cpt rtr).ids) : i ∈ (cpt? cpt (rtr : β)).ids :=
  ⟨h.choose, c.lower_cpt?_eq_some _ h.choose_spec⟩ 

theorem lift_cpt?_eq_none (cpt) {i : ID} 
    (h : b.cpt? cpt rtr i = none) : a.cpt? cpt rtr i = none := by
  cases cpt <;> try cases ‹Component.Valued›
  all_goals simp_all [cpt?, ←c.rcns, ←c.ports, ←c.acts, ←c.state] 
  simp [c.nest', Partial.map_val] at h
  exact h

theorem lift_cpt?_eq_some (cpt) {i : ID} {o : a.componentType cpt} 
    (h : b.cpt? cpt rtr i = some ↑o) : a.cpt? cpt rtr i = some o := by
  split at h <;> simp_all [cpt?, ←c.rcns, ←c.ports, ←c.acts, ←c.state]
  simp [c.nest', Partial.map_val] at h
  have ⟨_, _, h⟩ := h
  cases c.inj h
  assumption

theorem lift_nest_eq_some {i : ID} (h : b.nest rtr i = some n₂) : 
    ∃ n₁, (a.nest rtr i = some n₁) ∧ ((n₁ : β) = n₂) := by
  simp [c.nest', Partial.map_val] at h
  exact h

-- Note: This theorem excludes `cpt = .rtr`, because that case is harder than the other cases and we
--       only ever use this theorem for `cpt = .act` anyway.
theorem lift_mem_cpt?_ids (cpt) (h : i ∈ (b.cpt? cpt rtr).ids) (hc : cpt ≠ .rtr := by simp) : 
    i ∈ (a.cpt? cpt rtr).ids := by
  cases cpt <;> try cases ‹Component.Valued›  
  case rtr => contradiction
  all_goals exact ⟨h.choose, c.lift_cpt?_eq_some _ h.choose_spec⟩ 

end LawfulCoe

inductive Member [ReactorType α] (cpt : Component) (i : ID) : α → Type _ 
  | final : i ∈ (cpt? cpt rtr).ids → Member cpt i rtr
  | nest : (nest rtr₁ j = some rtr₂) → (m : Member cpt i rtr₂) → Member cpt i rtr₁

namespace Member

def fromLawfulCoe [ReactorType α] [ReactorType β] [c : LawfulCoe α β] {rtr : α} : 
    (Member cpt i rtr) → Member cpt i (rtr : β)
  | final h  => final (c.lower_mem_cpt?_ids _ h)
  | nest h m => nest (c.lower_cpt?_eq_some (cpt := .rtr) h) (fromLawfulCoe m)

variable [ReactorType α] [ReactorType β]

instance [c : LawfulCoe α β] {rtr : α} : Coe (Member cpt i rtr) (Member cpt i (rtr : β)) where
  coe := Member.fromLawfulCoe

inductive Equivalent : {rtr₁ : α} → {rtr₂ : β} → (Member cpt i rtr₁) → (Member cpt i rtr₂) → Prop 
  | final : Equivalent (.final h₁) (.final h₂)
  | nest {n₁ : α} {n₂ : β} {m₁ : Member cpt i n₁} {m₂ : Member cpt i n₂} :
    (h₁ : ReactorType.nest rtr₁ j = some n₁) → (h₂ : ReactorType.nest rtr₂ j = some n₂) → 
    (Equivalent m₁ m₂) → Equivalent (.nest h₁ m₁) (.nest h₂ m₂)

namespace Equivalent

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
    
theorem from_lawfulCoe [LawfulCoe α β] {rtr : α} (m : Member cpt i rtr) : 
    Equivalent m (m : Member cpt i (rtr : β)) := by
  induction m
  case final => constructor
  case nest e => simp [fromLawfulCoe, Equivalent.nest _ _ e]

end Equivalent
end Member

class Extensional (α) extends ReactorType α where
  ext_iff : 
    rtr₁ = rtr₂ ↔ 
    (ports rtr₁ = ports rtr₂) ∧ (acts rtr₁ = acts rtr₂) ∧ (state rtr₁ = state rtr₂) ∧ 
    (rcns rtr₁ = rcns rtr₂) ∧ (nest rtr₁ = nest rtr₂)

namespace Extensional

@[ext]
theorem ext [inst : Extensional α] {rtr₁ rtr₂ : α} : 
    (ports rtr₁ = ports rtr₂) ∧ (acts rtr₁ = acts rtr₂) ∧ (state rtr₁ = state rtr₂) ∧ 
    (rcns rtr₁ = rcns rtr₂) ∧ (nest rtr₁ = nest rtr₂) → rtr₁ = rtr₂ 
  := inst.ext_iff.mpr

instance [ReactorType α] [e : Extensional β] [c : LawfulCoe α β] : Extensional α where
  ext_iff := by
    intro rtr₁ rtr₂ 
    simp [c.coe_ext_iff, e.ext_iff, ←c.ports, ←c.acts, ←c.rcns, ←c.state, c.nest']
    intros
    exact {
      mp := Partial.map_inj (by simp [Function.Injective, c.coe_ext_iff])
      mpr := by simp_all
    }

end Extensional
end ReactorType