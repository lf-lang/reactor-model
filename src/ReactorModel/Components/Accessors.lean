import ReactorModel.Components.Reaction

open Classical
open Ports

-- `ι` and `υ` live in the same universe:
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Stuck.20at.20solving.20universe.20constraint/near/253232009
variable (ι υ : Type u) [ID ι] [Value υ]

-- The *type* corresponding to the component labeled by a given `Cmp`.
-- 
-- Note that the types for `prt` and `stateVar` are just `υ`, 
-- because IDs don't refer to entire instances of `Ports` or `StateVars`,
-- but rather the single values within them.
abbrev Cmp.type : Cmp → Type _
  | rtr => Reactor ι υ
  | rcn => Reaction ι υ
  | prt => υ
  | stv => υ

variable {ι υ}

namespace Reactor

-- This function returns (if possible) the ID of the reactor that contains
-- the component identified by a given ID `i` in the context of reactor `σ`.
-- The *kind* of component addressed by `i` is not required, as all IDs in a
-- reactor are unique.
--
-- Example: 
-- If `σ.containerOf i = some x`, then:
-- * `σ` is the "context" (top-level) reactor.
-- * `x` is the ID of a reactor which contains a reaction identified by `i`.
def containerOf (σ : Reactor ι υ) (i : ι) : Option ι := 
  sorry

-- This notation is chosen to be akin to the address notation in C,
-- because you get back a component's container's *identifier*, not the object.
notation σ:max " & " i:max => Reactor.containerOf σ i

-- This function returns (if possible) the object identified by a given ID `i` 
-- in the context of reactor `σ`. The *kind* of component addressed by `i` is
-- specified by parameter `cmp`.
--
-- Example: 
-- If `σ.objFor Cmp.rcn i = some x`, then:
-- * `σ` is the "context" (top-level) reactor.
-- * `i` is interpreted as being an ID that refers to a reaction (because of `Cmp.rcn`).
-- * `x` is the `Reaction` identified by `i`.
def objFor (σ : Reactor ι υ) (cmp : Cmp) : ι ▸ (cmp.type ι υ) := 
  sorry 
where 
  directObj (σ : Reactor ι υ) (cmp : Cmp) (i : ι) : Option (cmp.type ι υ) := 
    match cmp with
    | Cmp.rtr => σ.nest i
    | Cmp.rcn => σ.rcns i
    | Cmp.prt => σ.ports.lookup i -- TODO: Should this be a `lookup` or a `get`?
    | Cmp.stv => σ.state i

-- This notation is chosen to be akin to the dereference notation in C,
-- because you get back a component *object*.
notation σ:max " *[" c "]"  => Reactor.objFor σ c
notation σ:max " *[" c "] " i:max => Reactor.objFor σ c i

-- An extension on `objFor` for retrieving multiple objects at once.
noncomputable def objsFor (σ : Reactor ι υ) (cmp : Cmp) (is: Finset ι) : Finset (cmp.type ι υ) :=
  let description := { o : cmp.type ι υ | ∃ i ∈ is, σ *[cmp] i = o }
  let finite: description.finite := sorry
  finite.toFinset

notation σ:max " *[" c "] " is:max => Reactor.objsFor σ c is

-- A proposition stating that a given port (identified by `i`) has the given role `r`
-- within the context of a given reactor.
def portHasRole (σ : Reactor ι υ) (r : Ports.Role) (i : ι) : Prop :=
  ∃ (rcn : Reaction ι υ) (iᵣ : ι), σ *[Cmp.rcn] iᵣ = rcn ∧ i ∈ rcn.deps r 

def update (σ₁ σ₂ : Reactor ι υ) (cmp : Cmp) (i : ι) (v : cmp.type ι υ) : Prop := sorry
-- Needs recursion:
/-
  match σ₁ & i with
  | none => False
  | some p => 
    if p = ⊤
    then directUpdate σ₁ σ₂ cmp i v
    else
      σ₁.ports = σ₂.ports ∧ σ₂.roles = σ₁.roles ∧ σ₂.state = σ₁.state ∧ σ₂.prios = σ₁.prios ∧ σ₂.rcns = σ₁.rcns ∧ 
      ∀ σₚ ∈ σ₁.nest.entries, 
        if σₚ.snd & i = none
        then σₚ ∈ σ₂.nest.entries
        else update σₚ.snd σ₂ cmp i v
where
  directUpdate (σ₁ σ₂ : Reactor ι υ) (cmp : Cmp) (i : ι) (v : cmp.type ι υ) : Prop :=
    match cmp with 
      | Cmp.prt => sorry
        σ₂.ports = (σ₁.ports.update i v) ∧ 
        σ₂.roles = σ₁.roles ∧ σ₂.state = σ₁.state ∧ σ₂.nest = σ₁.nest ∧ σ₂.prios = σ₁.prios ∧ σ₂.rcns = σ₁.rcns
      | Cmp.rtr => sorry
        σ₂.nest = (σ₁.nest.update i v) ∧ 
        σ₂.ports = σ₁.ports ∧ σ₂.roles = σ₁.roles ∧ σ₂.state = σ₁.state ∧ σ₂.prios = σ₁.prios ∧ σ₂.rcns = σ₁.rcns
      | Cmp.stv => sorry
        σ₂.state = (σ₁.state.update i v) ∧ 
        σ₂.ports = σ₁.ports ∧ σ₂.roles = σ₁.roles ∧ σ₂.nest = σ₁.nest ∧ σ₂.prios = σ₁.prios ∧ σ₂.rcns = σ₁.rcns
      | Cmp.rcn => sorry
        σ₂.rcns = (σ₁.rcns.update i v) ∧ 
        σ₂.ports = σ₁.ports ∧ σ₂.roles = σ₁.roles ∧ σ₂.state = σ₁.state ∧ σ₂.nest = σ₁.nest ∧ σ₂.prios = σ₁.prios
-/

notation σ₁:max " -[" c ", " i " := " v "]→ " σ₂:max => Reactor.update σ₁ σ₂ c i v

end Reactor
