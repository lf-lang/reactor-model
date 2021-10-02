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

-- An implementation detail of `objFor`.
abbrev directObj (σ : Reactor ι υ) (cmp : Cmp) (i : ι) : Option (cmp.type ι υ) := 
  match cmp with
  | Cmp.rtr => σ.nest i
  | Cmp.rcn => σ.rcns i
  | Cmp.prt => σ.ports.lookup i -- TODO: Should this be a `lookup` or a `get`?
  | Cmp.stv => σ.state i

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

-- This notation is chosen to be akin to the dereference notation in C,
-- because you get back a component *object*.
notation σ:max " *[" c "]"  => Reactor.objFor σ c
notation σ:max " *[" c "] " i:max => Reactor.objFor σ c i

end Reactor

