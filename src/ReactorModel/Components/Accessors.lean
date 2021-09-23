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
@[reducible]
def Cmp.type : Cmp → Type _
  | rtr      => Reactor ι υ
  | rcn      => Reaction ι υ
  | prt _    => υ
  | stateVar => υ

variable {ι υ}

namespace Reactor

-- This function returns (if possible) the ID of the reactor that contains
-- the component identified by a given ID `i` in the context of reactor `rtr`.
-- The *kind* of component addressed by `i` is not required, as all IDs in a reactor are unique.
--
-- Example: 
-- If `r.containerOf i = some x`, then:
-- * `r` is the "context" (top-level) reactor.
-- * `x` is the ID of a reactor which contains a reaction identified by `i`.
noncomputable def containerOf (rtr : Reactor ι υ) (i : ι) : Option ι := 
  -- Don't define this in terms of `*ᵣ`.
  sorry

-- This notation is chosen to be akin to the address notation in C,
-- because you get back a component's *identifier*, not the object.
notation r " & " i => Reactor.containerOf r i

-- An implementation detail of `objFor`.
abbrev directObj (rtr : Reactor ι υ) (cmp : Cmp) (i : ι) : Option (cmp.type ι υ) := 
  match cmp with
  | Cmp.rtr => rtr.nest i
  | Cmp.rcn => rtr.rcns i
  | Cmp.prt r => (rtr.ports r).lookup i -- TODO: Should this be a `lookup` or a `get`?
  | Cmp.stateVar => rtr.state i

-- This function returns (if possible) the object identified by a given ID `i` 
-- in the context of reactor `rtr`. The *kind* of component addressed by `i`
-- is specified by parameter `cmp`.
--
-- Example: 
-- If `r.objFor Cmp.rcn i = some x`, then:
-- * `r` is the "context" (top-level) reactor.
-- * `i` is interpreted as being an ID that refers to a reaction (because of `Cmp.rcn`).
-- * `x` is the `Reaction` identified by `i`.
def objFor (rtr : Reactor ι υ) (cmp : Cmp) : ι ▸ (cmp.type ι υ) := 
  sorry 
/-
  if i = ⊤ then rtr else
    match (rtr &[c] i) with
    | none => none
    | some iₚ =>
      if iₚ = ⊤ then (directObj rtr c i) else
        match (rtr.objFor Cmp.rtr iₚ) with
        | none => none -- Unreachable
        | some p => directObj p c i
-/

-- This notation is chosen to be akin to the dereference notation in C,
-- because you get back a component *object*.
notation r " *[" c "]"   => Reactor.objFor r c
notation r " *[" c "]" i => Reactor.objFor r c i

-- The (finite) set of all valid IDs for a given type of component in a given (context) reactor.
noncomputable def allIDsFor (rtr : Reactor ι υ) (cmp : Cmp) : Finset ι := 
  let description := {i | (rtr *[cmp] i) ≠ none}
  let finite : description.finite := sorry
  finite.toFinset

notation r " & " c => Reactor.allIDsFor r c

end Reactor

