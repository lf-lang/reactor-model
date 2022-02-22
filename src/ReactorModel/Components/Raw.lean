import ReactorModel.Primitives
import ReactorModel.Time

structure Reaction.Input where
  portVals : ID ▸ Value
  acts : ID ▸ Value
  state : ID ▸ Value
  time : Time.Tag

namespace Raw

-- This block mainly serves the purpose of defining `Raw.Reactor`.
-- We later define an extension of `Raw.Reactor` called `Reactor`, which adds
-- all of the necessary constraints on it subcomponents.
-- Those subcomponents are then (re-)defined as well, by using the definition
-- of `Reactor`.
--
-- For more information on the use case of each component, cf. the definitions
-- of their non-`Raw` counterparts.
--
-- Side note:
-- The type class instances required by all types are named (`i` and `v`). This 
-- is necessary as Lean requires all type-level parameters of mutually inductive
-- definitions to have the same name. (So the `ID` and `Value` parameters also need to have
-- the same name across all definitions.)
mutual 

protected inductive Change 
  | port (target : ID) (value : Value)
  | action (target : ID) (time : Time) (value : Value)
  | state (target : ID) (value : Value)
  | connect (src : ID) (dst : ID)
  | disconnect (src : ID) (dst : ID)
  | create (rtr : Raw.Reactor)
  | delete (rtrID : ID)

protected inductive Reaction 
  | mk 
    (deps : Port.Role → Finset ID) 
    (triggers : Finset ID)
    (prio : Priority)
    (body : Reaction.Input → List Raw.Change)

protected inductive Reactor 
  | mk 
    (ports : ID ▸ Port) 
    (acts :  ID ▸ Time.Tag ▸ Value)
    (state : ID ▸ Value)
    (rcns :  ID → Option Raw.Reaction)
    (nest :  ID → Option Raw.Reactor)

end

end Raw

-- We add some basic necessities for raw components, so that they are more 
-- comfortable to work with in the process of defining "proper" components.
-- We try to limit these conveniences though, as they are superfluous as soon
-- as we have "proper" components.

-- Cf. `Change.mutates`.
def Raw.Change.mutates : Raw.Change → Bool
  | port ..       => false
  | state ..      => false
  | action ..     => false
  | connect ..    => true
  | disconnect .. => true
  | create ..     => true
  | delete ..     => true

namespace Raw.Reaction

-- These definitions give us the projections that would usually be generated for a structure.
def deps :     Raw.Reaction → Port.Role → Finset ID            | mk d _ _ _ => d
def triggers : Raw.Reaction → Finset ID                        | mk _ t _ _ => t
def prio :     Raw.Reaction → Priority                         | mk _ _ p _ => p
def body :     Raw.Reaction → Reaction.Input → List Raw.Change | mk _ _ _ b => b

-- Cf. `Reaction.isNorm`.
def isNorm (rcn : Raw.Reaction) : Prop :=
  ∀ i c, (c ∈ rcn.body i) → ¬c.mutates

-- Cf. `Reaction.isMut`.
def isMut (rcn : Raw.Reaction) : Prop :=
  ¬rcn.isNorm

-- Cf. `Reaction.isPure`.
structure isPure (rcn : Raw.Reaction) : Prop where
  input : ∀ p a s₁ s₂ t, rcn.body ⟨p, a, s₁, t⟩ = rcn.body ⟨p, a, s₂, t⟩ 
  output : ∀ i c, c ∈ rcn.body i → ∃ p v, c = Raw.Change.port p v

-- An extensionality theorem for `Raw.Reaction`.
theorem ext_iff {rcn₁ rcn₂ : Raw.Reaction} : 
  rcn₁ = rcn₂ ↔ 
  rcn₁.deps = rcn₂.deps ∧ rcn₁.triggers = rcn₂.triggers ∧ 
  rcn₁.prio = rcn₂.prio ∧ rcn₁.body = rcn₂.body := by
  constructor
  case mp =>
    intro h
    cases rcn₁
    cases rcn₂
    simp [h]
  case mpr =>
    intro h
    simp only [deps, triggers, prio, body] at h
    cases rcn₁
    cases rcn₂
    simp [h]

-- We need this additional theorem as the `ext` attribute can only be used on theorems proving an equality.
@[ext]
theorem ext {rcn₁ rcn₂ : Raw.Reaction} :
  rcn₁.deps = rcn₂.deps ∧ rcn₁.triggers = rcn₂.triggers ∧ 
  rcn₁.prio = rcn₂.prio ∧ rcn₁.body = rcn₂.body → rcn₁ = rcn₂ :=
  λ h => ext_iff.mpr h  

end Raw.Reaction

namespace Raw.Reactor

-- These definitions give us the projections that would usually be generated for a structure.
def ports : Raw.Reactor → ID ▸ Port                | mk p _ _ _ _ => p
def acts :  Raw.Reactor → ID ▸ Time.Tag ▸ Value    | mk _ a _ _ _ => a
def state : Raw.Reactor → ID ▸ Value               | mk _ _ s _ _ => s 
def rcns :  Raw.Reactor → ID → Option Raw.Reaction | mk _ _ _ r _ => r
def nest :  Raw.Reactor → ID → Option Raw.Reactor  | mk _ _ _ _ n => n

noncomputable def ports' (rtr : Raw.Reactor) (r : Port.Role) : ID ▸ Port := 
  rtr.ports.filter' (·.role = r)

-- Cf. `Reactor.portVals`.
noncomputable def portVals (rtr : Raw.Reactor) (r : Port.Role) : ID ▸ Value := 
  (rtr.ports' r).map Port.val

-- An extensionality theorem for `Raw.Reactor`.
theorem ext_iff {rtr₁ rtr₂ : Raw.Reactor} : 
  rtr₁ = rtr₂ ↔ 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts ∧ 
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns = rtr₂.rcns ∧ 
  rtr₁.nest  = rtr₂.nest := by
  constructor
  case mp =>
    intro h
    cases rtr₁
    cases rtr₂
    simp [h]
  case mpr =>
    intro h
    simp [ports, state, rcns, acts, nest] at h
    cases rtr₁
    cases rtr₂
    simp [h]

-- We need this additional theorem as the `ext` attribute can only be used on theorems proving an equality.
@[ext]
theorem ext {rtr₁ rtr₂ : Raw.Reactor} :
  rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts  ∧ 
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns = rtr₂.rcns  ∧ 
  rtr₁.nest  = rtr₂.nest → 
  rtr₁ = rtr₂ :=
  λ h => ext_iff.mpr h  

end Raw.Reactor