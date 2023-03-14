import ReactorModel.Objects.Reaction

namespace Reactor

inductive Component.Valued
  | prt (k : Kind) -- Ports
  | act            -- Actions
  | stv            -- State variables 

-- An enumeration of the different *kinds* of components that are addressable by ids in a reactor.
inductive Component
  | val (v : Component.Valued)
  | rtr -- Nested reactors
  | rcn -- Reactions

namespace Component

abbrev Valued.type : Valued → Type
  | .prt _ => Value
  | .act   => Time.Tag ⇉ Value
  | .stv   => Value

@[match_pattern] abbrev prt (k) := Component.val (.prt k)
@[match_pattern] abbrev act     := Component.val .act
@[match_pattern] abbrev stv     := Component.val .stv

instance : Coe Component.Valued Component where
  coe := val 

abbrev idType : Component → Type
  | rtr => RootedID
  | _   => ID

instance {cmp : Component} : Coe ID cmp.idType where
  coe i :=
    match cmp with
    | .rtr => .nest i
    | .rcn | .val _ => i

end Component
end Reactor

open Reactor (Component)

class ReactorType (α : Type) where
  ports : α → Kind → ID ⇀ Value             
  acts  : α → ID ⇀ Time.Tag ⇉ Value 
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
  | .val cmp => cmp.type

abbrev cmp? [inst : ReactorType α] : (cmp : Component) → α → ID ⇀ inst.componentType cmp
  | .rtr   => nest 
  | .rcn   => rcns
  | .prt k => (ports · k)
  | .act   => acts
  | .stv   => state

namespace LawfulCoe

variable [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] {rtr : α}

instance {cmp} : Coe (a.componentType cmp) (b.componentType cmp) where
  coe := 
    match cmp with
    | .rcn | .prt _ | .act | .stv => id
    | .rtr => c.coe

theorem lower_cmp?_eq_some (cmp) {o} (h : a.cmp? cmp rtr i = some o) : 
    b.cmp? cmp rtr i = some ↑o := by
  split <;> simp_all [cmp?, ←c.rcns, ←c.ports, ←c.acts, ←c.state]
  simp [c.nest', Partial.map_val]
  exists o

theorem lower_mem_cmp?_ids (cmp) (h : i ∈ (cmp? cmp rtr).ids) : i ∈ (cmp? cmp (rtr : β)).ids :=
  ⟨h.choose, c.lower_cmp?_eq_some _ h.choose_spec⟩ 

theorem lift_cmp?_eq_some (cmp) {i : ID} {o : a.componentType cmp} 
    (h : b.cmp? cmp rtr i = some ↑o) : a.cmp? cmp rtr i = some o := by
  split at h <;> simp_all [cmp?, ←c.rcns, ←c.ports, ←c.acts, ←c.state]
  simp [c.nest', Partial.map_val] at h
  have ⟨_, _, h⟩ := h
  cases c.inj h
  assumption

-- Note: This theorem excludes `cmp = .rtr`, because that case is harder than the other cases and we
--       only ever use this theorem for `cmp = .act` anyway.
theorem lift_mem_cmp?_ids (cmp) (h : i ∈ (b.cmp? cmp rtr).ids) (hc : cmp ≠ .rtr := by simp) : 
    i ∈ (a.cmp? cmp rtr).ids := by
  cases cmp <;> try cases ‹Component.Valued›  
  case rtr => contradiction
  all_goals exact ⟨h.choose, c.lift_cmp?_eq_some _ h.choose_spec⟩ 

end LawfulCoe

inductive Lineage [ReactorType α] (cmp : Component) (i : ID) : α → Type _ 
  | final : i ∈ (cmp? cmp rtr).ids → Lineage cmp i rtr
  | nest : (nest rtr₁ j = some rtr₂) → (Lineage cmp i rtr₂) → Lineage cmp i rtr₁

namespace Lineage

def fromLawfulCoe [ReactorType α] [ReactorType β] [c : LawfulCoe α β] 
    {rtr : α} {cmp} : (Lineage cmp i rtr) → Lineage cmp i (rtr : β)
  | final h  => final (c.lower_mem_cmp?_ids _ h)
  | nest h l => nest (c.lower_cmp?_eq_some (cmp := .rtr) h) (fromLawfulCoe l)

variable [ReactorType α] [ReactorType β] {cmp : Component}

instance [c : LawfulCoe α β] {rtr : α} : Coe (Lineage cmp i rtr) (Lineage cmp i (rtr : β)) where
  coe := Lineage.fromLawfulCoe

inductive Equivalent : {rtr₁ : α} → {rtr₂ : β} → (Lineage cmp i rtr₁) → (Lineage cmp i rtr₂) → Prop 
  | final : Equivalent (.final h₁) (.final h₂)
  | nest {n₁ : α} {n₂ : β} {l₁ : Lineage cmp i n₁} {l₂ : Lineage cmp i n₂} :
    (h₁ : ReactorType.nest rtr₁ j = some n₁) → (h₂ : ReactorType.nest rtr₂ j = some n₂) → 
    (Equivalent l₁ l₂) → Equivalent (.nest h₁ l₁) (.nest h₂ l₂)

namespace Equivalent

theorem symm {rtr₁ : α} {rtr₂ : β} {cmp} {l₁ : Lineage cmp i rtr₁} {l₂ : Lineage cmp i rtr₂}
    (e : Equivalent l₁ l₂) : (Equivalent l₂ l₁) := by
  induction e <;> constructor; assumption

theorem trans 
    [ReactorType γ] {rtr₁ : α} {rtr₂ : β} {rtr₃ : γ}
    {l₁ : Lineage cmp i rtr₁} {l₂ : Lineage cmp i rtr₂} {l₃ : Lineage cmp i rtr₃}
    (e₁ : Equivalent l₁ l₂) (e₂ : Equivalent l₂ l₃) : (Equivalent l₁ l₃) := by
  induction e₁ generalizing l₃ rtr₃ <;> cases e₂ <;> constructor
  case nest.nest hi₁ _ _ _ _ hi₂ => exact hi₁ hi₂

-- Lemma for `to_eq`.
private theorem to_eq' {rtr₁ rtr₂ : α} {l₁ : Lineage cmp i rtr₁} {l₂ : Lineage cmp i rtr₂} 
    (h : rtr₁ = rtr₂) (e : Equivalent l₁ l₂) : l₁ = cast (by simp [h]) l₂ := by
  induction e <;> subst h
  case final => rfl
  case nest l₁ _ h₁ _ hi h₂ => 
    injection h₁ ▸ h₂ with h
    simp [hi h, h]

theorem to_eq {rtr : α} {l₁ l₂ : Lineage cmp i rtr} (e : Equivalent l₁ l₂) : l₁ = l₂ := 
  e.to_eq' rfl
    
theorem from_lawfulCoe [LawfulCoe α β] {rtr : α} (l : Lineage cmp i rtr) : 
    Equivalent l (l : Lineage cmp i (rtr : β)) := by
  induction l
  case final => constructor
  case nest e => simp [fromLawfulCoe, Equivalent.nest _ _ e]

end Equivalent
end Lineage

class Extensional (α : Type) extends ReactorType α where
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

theorem induction [Extensional α] {motive : α → Prop}
    (base : ∀ rtr, (nest rtr = ∅) → motive rtr)
    (step : ∀ rtr, (∀ i n, nest rtr i = some n → motive n) → motive rtr) :
    ∀ rtr, motive rtr :=
  sorry

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