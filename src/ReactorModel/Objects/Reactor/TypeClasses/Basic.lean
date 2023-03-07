import ReactorModel.Objects.Reaction

namespace Reactor

-- An enumeration of the different *kinds* of components that are addressable by ids in a reactor.
inductive Component
  | rtr -- Nested reactors
  | rcn -- Reactions
  | prt -- Ports
  | act -- Actions
  | stv -- State variables

namespace Component

abbrev idType : Component → Type _
  | rtr => RootedID
  | _   => ID

instance {cmp : Component} : Coe ID cmp.idType where
  coe i :=
    match cmp with
    | .rtr => .nest i
    | .rcn | .prt | .act | .stv => i

end Component
end Reactor

open Reactor (Component)

class ReactorType (α : Type _) where
  ports : α → ID ⇀ Port             
  acts :  α → ID ⇀ Time.Tag ⇀ Value 
  state : α → ID ⇀ Value            
  rcns :  α → ID ⇀ Reaction         
  nest :  α → ID ⇀ α      

namespace ReactorType

scoped macro "lawfulCoe_nest_proof" : tactic => 
  `(tactic| simp [ReactorType.nest, Partial.map_map, Function.comp, Partial.attach_map_val])

protected class LawfulCoe (α β) [a : ReactorType α] [b : ReactorType β] extends Coe α β where
  ports : b.ports ∘ coe = a.ports                    := by rfl
  acts  : b.acts  ∘ coe = a.acts                     := by rfl
  rcns  : b.rcns  ∘ coe = a.rcns                     := by rfl
  state : b.state ∘ coe = a.state                    := by rfl
  nest  : b.nest  ∘ coe = (Partial.map coe) ∘ a.nest := by lawfulCoe_nest_proof

theorem LawfulCoe.nest' [a : ReactorType α] [b : ReactorType β] [c : ReactorType.LawfulCoe α β] :
    b.nest (c.coe rtr) = (a.nest rtr).map c.coe := by
  rw [←Function.comp_apply (f := ReactorType.nest), c.nest]
  simp

class Extensional (α) extends ReactorType α where
  ext_iff : 
    rtr₁ = rtr₂ ↔ 
    (ports rtr₁ = ports rtr₂) ∧ (acts rtr₁ = acts rtr₂) ∧ (state rtr₁ = state rtr₂) ∧ 
    (rcns rtr₁ = rcns rtr₂) ∧ (nest rtr₁ = nest rtr₂)

@[ext]
theorem Extensional.ext [inst : Extensional α] {rtr₁ rtr₂ : α} : 
    (ports rtr₁ = ports rtr₂) ∧ (acts rtr₁ = acts rtr₂) ∧ (state rtr₁ = state rtr₂) ∧ 
    (rcns rtr₁ = rcns rtr₂) ∧ (nest rtr₁ = nest rtr₂) → rtr₁ = rtr₂ 
  := inst.ext_iff.mpr

protected class Extensional.LawfulCoe (α β) [ReactorType α] [Extensional β] 
    extends ReactorType.LawfulCoe α β where
  coe_ext_iff : rtr₁ = rtr₂ ↔ (coe rtr₁ = coe rtr₂)

instance [ReactorType α] [e : Extensional β] [c : Extensional.LawfulCoe α β] : Extensional α where
  ext_iff := by
    intro rtr₁ rtr₂ 
    simp [c.coe_ext_iff, e.ext_iff, ←c.ports, ←c.acts, ←c.rcns, ←c.state, c.nest']
    intros
    exact {
      mp := Partial.map_inj (by simp [Function.Injective, c.coe_ext_iff])
      mpr := by simp_all
    }

abbrev componentType [ReactorType α] : Component → Type _
  | .rtr => α 
  | .rcn => Reaction
  | .prt => Port
  | .act => Time.Tag ⇀ Value
  | .stv => Value

abbrev cmp? [inst : ReactorType α] : (cmp : Component) → α → ID ⇀ inst.componentType cmp
  | .rtr => nest 
  | .rcn => rcns
  | .prt => ports
  | .act => acts
  | .stv => state

inductive Lineage [ReactorType α] (cmp : Component) (i : ID) : α → Type _ 
  | final : i ∈ (cmp? cmp rtr).ids → Lineage cmp i rtr
  | nest : (nest rtr₁ j = some rtr₂) → (Lineage cmp i rtr₂) → Lineage cmp i rtr₁

theorem LawfulCoe.lower_nest_eq_some 
    [a : ReactorType α] [b : ReactorType β] [c : ReactorType.LawfulCoe α β] {rtr₁ rtr₂ : α}
    (h : a.nest rtr₁ i = some rtr₂) : b.nest (rtr₁ : β) i = some (rtr₂ : β) := by
  simp [c.nest', Partial.map_val]
  exists rtr₂

theorem LawfulCoe.lower_mem_cmp?_ids 
    [a : ReactorType α] [ReactorType β] [c : ReactorType.LawfulCoe α β] {rtr : α} : 
    {cmp : Component} → (i ∈ (cmp? cmp rtr).ids) → i ∈ (cmp? cmp (rtr : β)).ids
  | .rcn, h => by simp_all [cmp?, ←c.rcns]
  | .prt, h => by simp_all [cmp?, ←c.ports]
  | .act, h => by simp_all [cmp?, ←c.acts]
  | .stv, h => by simp_all [cmp?, ←c.state]
  | .rtr, h => by
    simp [cmp?, Partial.mem_ids_iff] at h ⊢ 
    exact ⟨h.choose, c.lower_nest_eq_some h.choose_spec⟩ 

namespace Lineage

def container [ReactorType α] {cmp} {rtr : α} : Lineage cmp i rtr → Identified α
  | nest _ (nest h l)              => container (nest h l)
  | nest (rtr₁ := con) (j := j) .. => { id := j, obj := con }
  | _                              => { id := ⊤, obj := rtr }

def fromLawfulCoe [ReactorType α] [ReactorType β] [c : ReactorType.LawfulCoe α β] 
    {rtr : α} {cmp} : (Lineage cmp i rtr) → Lineage cmp i (rtr : β)
  | final h  => final (c.lower_mem_cmp?_ids h)
  | nest h l => nest (c.lower_nest_eq_some h) (fromLawfulCoe l)

inductive Equivalent [ReactorType α] [ReactorType β] {cmp} : 
    {rtr₁ : α} → {rtr₂ : β} → (Lineage cmp i rtr₁) → (Lineage cmp i rtr₂) → Prop 
  | final : Equivalent (.final h₁) (.final h₂)
  | nest {n₁ : α} {n₂ : β} {l₁ : Lineage cmp i n₁} {l₂ : Lineage cmp i n₂} :
    (h₁ : ReactorType.nest rtr₁ j = some n₁) → (h₂ : ReactorType.nest rtr₂ j = some n₂) → 
    (Equivalent l₁ l₂) → Equivalent (.nest h₁ l₁) (.nest h₂ l₂)

namespace Equivalent

theorem symm [ReactorType α] [ReactorType β]
    {rtr₁ : α} {rtr₂ : β} {cmp} {l₁ : Lineage cmp i rtr₁} {l₂ : Lineage cmp i rtr₂}
    (e : Equivalent l₁ l₂) : (Equivalent l₂ l₁) := by
  induction e <;> constructor; assumption

theorem trans [ReactorType α] [ReactorType β] [ReactorType γ] 
    {rtr₁ : α} {rtr₂ : β} {rtr₃ : γ} {cmp} 
    {l₁ : Lineage cmp i rtr₁} {l₂ : Lineage cmp i rtr₂} {l₃ : Lineage cmp i rtr₃}
    (e₁ : Equivalent l₁ l₂) (e₂ : Equivalent l₂ l₃) : (Equivalent l₁ l₃) := by
  induction e₁ generalizing l₃ rtr₃ <;> cases e₂ <;> constructor
  case nest.nest hi₁ _ _ _ _ hi₂ => exact hi₁ hi₂

-- Lemma for `to_eq`.
private theorem to_eq' [ReactorType α] {cmp} {rtr₁ rtr₂ : α} 
    {l₁ : Lineage cmp i rtr₁} {l₂ : Lineage cmp i rtr₂} (h : rtr₁ = rtr₂) (e : Equivalent l₁ l₂) : 
    l₁ = cast (by simp [h]) l₂ := by
  induction e <;> subst h
  case final => rfl
  case nest l₁ _ h₁ _ hi h₂ => 
    injection h₁ ▸ h₂ with h
    simp [hi h, h]

theorem to_eq [ReactorType α] {cmp} {rtr : α} 
    {l₁ l₂ : Lineage cmp i rtr} (e : Equivalent l₁ l₂) : l₁ = l₂ := 
  e.to_eq' rfl
    
theorem from_lawfulCoe [ReactorType α] [ReactorType β] [ReactorType.LawfulCoe α β] {rtr : α} {cmp} 
    (l : Lineage cmp i rtr) : Equivalent l (Lineage.fromLawfulCoe l : Lineage _ _ (rtr : β)) := by
  induction l
  case final => constructor
  case nest e => simp [fromLawfulCoe, Equivalent.nest _ _ e]

end Equivalent
end Lineage

def UniqueIDs [ReactorType α] (rtr : α) : Prop :=
  ∀ {cmp i}, Subsingleton (Lineage cmp i rtr)

theorem UniqueIDs.lift [ReactorType α] [ReactorType β] [ReactorType.LawfulCoe α β]
    {rtr : α} (h : UniqueIDs (rtr : β)) : UniqueIDs rtr where
  allEq l₁ l₂ :=
    h.allEq (.fromLawfulCoe l₁) (.fromLawfulCoe l₂) ▸ Lineage.Equivalent.from_lawfulCoe l₁ 
      |>.trans (Lineage.Equivalent.from_lawfulCoe l₂).symm 
      |>.to_eq

end ReactorType