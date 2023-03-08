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

abbrev idType : Component → Type
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

class ReactorType (α : Type) where
  ports : α → ID ⇀ Port             
  acts :  α → ID ⇀ Time.Tag ⇀ Value 
  state : α → ID ⇀ Value            
  rcns :  α → ID ⇀ Reaction         
  nest :  α → ID ⇀ α      

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

class Extensional (α : Type) extends ReactorType α where
  ext_iff : 
    rtr₁ = rtr₂ ↔ 
    (ports rtr₁ = ports rtr₂) ∧ (acts rtr₁ = acts rtr₂) ∧ (state rtr₁ = state rtr₂) ∧ 
    (rcns rtr₁ = rcns rtr₂) ∧ (nest rtr₁ = nest rtr₂)

@[ext]
theorem Extensional.ext [inst : Extensional α] {rtr₁ rtr₂ : α} : 
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

abbrev componentType [ReactorType α] : Component → Type
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

instance [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] {cmp : Component} :
    Coe (a.componentType cmp) (b.componentType cmp) where
  coe := 
    match cmp with
    | .rcn | .prt | .act | .stv => id
    | .rtr => c.coe

theorem LawfulCoe.lower_cmp?_eq_none
    [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] {rtr : α} (cmp)
    (h : a.cmp? cmp rtr i = none) : b.cmp? cmp rtr i = none := by
  cases cmp <;> simp_all [cmp?, ←c.rcns, ←c.ports, ←c.acts, ←c.state]
  simp [c.nest', Partial.map_val]
  assumption

theorem LawfulCoe.lower_cmp?_eq_some
    [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] {rtr : α} (cmp) {o}
    (h : a.cmp? cmp rtr i = some o) : b.cmp? cmp rtr i = some ↑o := by
  split <;> simp_all [cmp?, ←c.rcns, ←c.ports, ←c.acts, ←c.state]
  simp [c.nest', Partial.map_val]
  exists o

theorem LawfulCoe.lower_mem_cmp?_ids 
    [a : ReactorType α] [ReactorType β] [c : LawfulCoe α β] {rtr : α} (cmp)
    (h : i ∈ (cmp? cmp rtr).ids) : i ∈ (cmp? cmp (rtr : β)).ids :=
  ⟨h.choose, c.lower_cmp?_eq_some _ h.choose_spec⟩ 

theorem LawfulCoe.lift_cmp?_eq_some 
    [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] (cmp) {i : ID} {rtr : α}
    {o : a.componentType cmp} (h : b.cmp? cmp rtr i = some ↑o) : a.cmp? cmp rtr i = some o := by
  split at h <;> simp_all [cmp?, ←c.rcns, ←c.ports, ←c.acts, ←c.state]
  simp [c.nest', Partial.map_val] at h
  have ⟨_, _, h⟩ := h
  cases c.inj h
  assumption

-- Note: This theorem exludes `cmp = .rtr`, because that case is harder than the others and we only
--       ever use this theorem for `cmp = .act` anyway.
theorem LawfulCoe.lift_mem_cmp?_ids [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] 
    (cmp) {rtr : α} (h : i ∈ (b.cmp? cmp rtr).ids) (hc : cmp ≠ .rtr := by simp) : 
    i ∈ (a.cmp? cmp rtr).ids := by
  cases cmp 
  case rtr => contradiction
  all_goals exact ⟨h.choose, c.lift_cmp?_eq_some _ h.choose_spec⟩ 

inductive Lineage [ReactorType α] (cmp : Component) (i : ID) : α → Type _ 
  | final : i ∈ (cmp? cmp rtr).ids → Lineage cmp i rtr
  | nest : (nest rtr₁ j = some rtr₂) → (Lineage cmp i rtr₂) → Lineage cmp i rtr₁

namespace Lineage

def fromLawfulCoe [ReactorType α] [ReactorType β] [c : LawfulCoe α β] 
    {rtr : α} {cmp} : (Lineage cmp i rtr) → Lineage cmp i (rtr : β)
  | final h  => final (c.lower_mem_cmp?_ids _ h)
  | nest h l => nest (c.lower_cmp?_eq_some (cmp := .rtr) h) (fromLawfulCoe l)

-- TODO: Delete this if it remains unused.
theorem nonempty_from_lawfulCoe 
    [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} {cmp}
    (h : Nonempty $ Lineage cmp i rtr) : Nonempty $ Lineage cmp i (rtr : β) :=
  h.elim (.intro $ .fromLawfulCoe ·)

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

theorem trans [ReactorType α] [ReactorType β] [ReactorType γ] {rtr₁ : α} {rtr₂ : β} {rtr₃ : γ} {cmp} 
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
    
theorem from_lawfulCoe [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} {cmp} 
    (l : Lineage cmp i rtr) : Equivalent l (Lineage.fromLawfulCoe l : Lineage _ _ (rtr : β)) := by
  induction l
  case final => constructor
  case nest e => simp [fromLawfulCoe, Equivalent.nest _ _ e]

end Equivalent
end Lineage

def UniqueIDs [ReactorType α] (rtr : α) : Prop :=
  ∀ {cmp i}, Subsingleton (Lineage cmp i rtr)

theorem UniqueIDs.lift [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} 
    (h : UniqueIDs (rtr : β)) : UniqueIDs rtr where
  allEq l₁ l₂ :=
    h.allEq (.fromLawfulCoe l₁) (.fromLawfulCoe l₂) ▸ Lineage.Equivalent.from_lawfulCoe l₁ 
      |>.trans (Lineage.Equivalent.from_lawfulCoe l₂).symm 
      |>.to_eq

end ReactorType