import ReactorModel.Components.Lift

open Classical

variable {ι υ} [ID ι] [Value υ]

-- A non-`Raw` accessor for a `Reactor`'s mutations.
def Reactor.rcns (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  let raw : Finmap ι (Raw.Reaction ι υ) := { lookup := rtr.raw.rcns, finite := rtr.wf.direct.rcnsFinite }
  raw.map' $ λ rcn h => Reaction.fromRaw rtr.wf (Finmap.values_def.mp h)

noncomputable def Reactor.norms (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isNorm)

noncomputable def Reactor.muts (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isMut)  

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

-- Associates each type of component with the finmap in which it can be
-- found inside of a reactor.
-- We use this in `objFor` to generically resolve the lookup for *some*
-- component and *some* ID.
abbrev Cmp.accessor : (cmp : Cmp) → Reactor ι υ → (ι ▸ cmp.type ι υ)
  | Cmp.rtr => Reactor.nest
  | Cmp.rcn => Reactor.rcns
  | Cmp.prt => Reactor.ports -- TODO: Should this be a `lookup` or a `get`?
  | Cmp.stv => Reactor.state

variable {ι υ}

namespace Reactor

structure IDPath (σ : Reactor ι υ) (i : ι) (cmp : Cmp) where
  path : List ι
  wf : path ~ᵣ[σ.raw, cmp] i

-- Returns the reactor that matches the last ID in the ID-path.
def IDPath.resolve {σ i cmp} (p : IDPath (ι := ι) (υ := υ) σ i cmp) : Reactor ι υ :=
  sorry

-- This function returns (if possible) the ID of the reactor that contains
-- the component identified by a given ID `i` in the context of reactor `σ`.
-- The *kind* of component addressed by `i` is not required, as all IDs in a
-- reactor are unique.
--
-- Example: 
-- If `σ.containerOf i = some x`, then:
-- * `σ` is the "context" (top-level) reactor.
-- * `x` is the ID of a reactor which contains a reaction identified by `i`.
--
-- Explanation:
-- We use the concept of reactor-ID-paths (cf. `isRtrIDPathFor`) to "find"
-- the path of reactor-IDs that leads us through `σ` to reach `i`.
-- If such a path exists we return the ID of the last reactor in that path,
-- because by definition of reactor-ID-paths, *that* is reactor that contains
-- `i`. If the ID-path is empty, `i` must live in `σ` itself, so we return the
-- top-level reactor-ID `⊤`. If no path could be found, we return `none`.
--
-- Note that since a `Reactor` ensures ID-uniqueness (via `wf.direct.uniqueIDs`),
-- the choice of path reactor-ID-path `h.choose` is always unique.
-- That is, we could define `containerOf` as a relation and prove that it is
-- functional by using `wf.direct.uniqueIDs`. But defining it directly as a
-- function using the axiom of choice seems good enough.
noncomputable def containerOf (σ : Reactor ι υ) (i : ι) : Option ι := 
  if h : ∃ (cmp : Cmp), Nonempty (IDPath σ i cmp) 
  then (Classical.choice h.choose_spec).path.getLastD ⊤ 
  else none

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
noncomputable def objFor (σ : Reactor ι υ) (cmp : Cmp) : ι ▸ (cmp.type ι υ) := {
  lookup := λ i => 
    if h : Nonempty (IDPath σ i cmp) 
    then cmp.accessor (ι := ι) (υ := υ) (Classical.choice h).resolve i
    else none,
  finite := sorry
} 

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

end Reactor
