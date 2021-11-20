# Reactor Components

While the previous document on the [Formalization Structure](1.%20Formalization%20Structure.md)
explains how and why the components of the Reactor model are formalized in a certain way,
it generally ignores the nature of the components themselves.
In this document we intend to do the opposite: We take a look at each of the components of
the Reactor model in detail, while generally ignoring the technicalities of the larger 
formalization structure. There are three components to consider: `Change`, `Reaction` and `Reactor`.

## `Change`

In the semi-formal definition of the Reactor model, reactions' bodies are defined as "opaque code" that
has access to a set of APIs for settings ports' values, connecting ports, creating reactors, etc.
The definition of a reaction's body used in *this* formalization is as a function of type
`Ports ι υ → StateVars ι υ → List (Change ι υ)` (as we will see in [`Reaction` (and Mutations)](#reaction-and-mutations)).
That is, we ignore all side effects that a reaction could have and only consider the part that is
relevant to the reactor system: the API calls. These API calls are formalized by the `Change` type:

```lean
-- Components/Change.lean

inductive Change (ι υ) [ID ι] [Value υ]
  | port (target : ι) (value : υ)
  | state (target : ι) (value : υ)
  | connect (src : ι) (dst : ι)
  | disconnect (src : ι) (dst : ι)
  | create (rtr : Reactor ι υ) (id : ι)
  | delete (rtrID : ι)
```

Thus, if a reaction were to call the API for setting a port's value, we would formalize this as returning
an instance `Change.port <target> <value>`. Since a reaction can perform multiple API calls per execution,
it returns a `List` of `Change`s.

Instances of `Change` can be split into two groups: those which express a mutation to the structure of a
reactor system, and those which don't:

```lean
def Change.mutates : Change ι υ → Bool 
  | port _ _       => false
  | state _ _      => false
  | connect _ _    => true
  | disconnect _ _ => true
  | create _ _     => true
  | delete _       => true
```

This distinction will be used later to differentiate between "normal" reactions and mutations, as normal
reactions are not allowed to produce mutating changes.
The actual behavior that should result from applying a `Change` will be part of the execution model of reactors.

## `Reaction` (and Mutations)

The components that can produce changes in a reactor system are reactions:

```lean
-- Components/Reaction.lean

structure Reaction (ι υ) [ID ι] [Value υ] where
  deps :        Ports.Role → Finset ι 
  triggers :    Finset ι
  children :    Finset ι
  body :        Ports ι υ → StateVars ι υ → List (Change ι υ)
  tsSubInDeps : triggers ⊆ deps Role.in
  outDepOnly :  ∀ p s {o} (v : υ), (o ∉ deps Role.out) → (Change.port o v) ∉ (body p s)
  normNoChild : (∀ i s c, c ∈ (body i s) → ¬c.mutates) → children = ∅
```

Reactions can have dependencies and antidependencies on ports. 
The `deps` field defines both kinds of dependencies by referring to the ports' identifiers and separating
these identifiers by the "role" of the port they refer to.
A `Ports.Role` is simply a utility type used for exactly these kinds of separations:

```lean
-- Primitives.lean

inductive Ports.Role 
  | «in» 
  | out
```

A reaction declares a set of `triggers`, which are a subset of its input ports.
The subset-property is enforced by `tsSubInDeps`.

Thus, we can define properties like `triggersOn` which defines when a given port assignment triggers
a reaction:

```lean
def Reaction.triggersOn (rcn : Reaction ι υ) (p : Ports ι υ) : Prop :=
  ∃ t, t ∈ rcn.triggers ∧ p[t] ≠ none
```

> The notation `p[t]` is `Ports.get` defined in `Primitives.lean`.
> You can think of it as lookup for a port value given a port ID.

### Reaction Body

A reaction's `body` is the function that describes its behavior in terms of the `Change`s it produces.
The inputs to the function are port values (`Ports ι υ`) and values for state variables
(`StateVars ι υ`). In the context of an execution of a reactor, the arguments to a reaction's `body`
will be input ports and state variables of the reactor that contains the reaction. The definition of
execution will ensure that we only pass in those input ports which are dependencies of the reaction (by
using `Finmap.restrict`).

> Note:
> We could have also defined a reaction's body in such a way that it accepts as inputs only
> precisely those ports (their values) which are declared in its dependencies.
> This is more cumbersome to work with at the call site though.

To ensure that a reaction's body only produces valid changes, we need to enforce some constraints:

* `outDepOnly`: The reaction can only write to ports that are in its antidependencies.
* TODO: Can constraints on `Change.{state, connect, disconnect, create, delete}` be moved from the
        execution model to here? I.e. which ones can LF figure out statically?

To make calling a reaction's body more convenient, we add a coercion that allows us to use call syntax
on the reaction itself:

```lean
instance : CoeFun (Reaction ι υ) (λ _ => Ports ι υ → StateVars ι υ → (List (Change ι υ))) where
  coe rcn := rcn.body
```

So when you see something like `rcn p s` that's the same as `rcn.body p s`.

### Mutations

In the section on `Changes` we defined a property that told us whether a change is mutating or not
(`Change.mutates`). We need this information in order to distinguish "normal" reactions from mutations.

We say that a reaction is "normal" if it produces no mutating changes:

```lean
def Reaction.isNorm (rcn : Reaction ι υ) : Prop :=
  ∀ i s c, c ∈ (rcn i s) → ¬c.mutates
```

We then say that a reaction is a mutation if it is not "normal":

```lean
def Reaction.isMut (rcn : Reaction ι υ) : Prop := ¬rcn.isNorm
```

Thus, `Reaction` is the type of "normal" reactions *and* mutations.
Whenever we want to talk about only one of these flavors, we require `isNorm` or `isMut` on the reaction.

One example of this is within the very definition of `Reaction`, to constrain the `children` field.
Children are a concept that only applies to mutations.
When mutations produce a `Change.create <reactor> <id>`, they need to remember the ID of the reactor they
created (for reasons that are related to the execution model). These IDs are recorded in their `children`
field. Since "normal" reactions can't create reactors (since this is a mutating change), they can't have
children. This is enforced by:

```lean
normNoChild : (∀ i s c, c ∈ (body i s) → ¬c.mutates) → children = ∅
```

The condition `∀ i s c, c ∈ (body i s) → ¬c.mutates` is precisely the definition of `Reaction.isNorm` (we
couldn't use `isNorm` in the definition of `Reaction` yet, as this would be circular).

### Relay Reactions

Relay reactions are a specific kind of reaction that allow us to simplify what it means for reactors' ports to be connected.
In the semi-formal definition of the Reactor model we say that reactors can contain nested reactors where the output ports of
a nested reactor can have a "connection" to an input port of another nested reactor.

This explicit notion of a "connection" can be removed by exploiting the way in which reactions can interact with nested reactors:
A reaction can declare as dependency an input port of its container or *an output port of a nested reactor* of its container.
Analogously, a reaction can declare as antidependency an output port of its container or *an input port of a nested reactor* of its container.
Thus, we can formalize connections between reactors' ports by creating a reaction that declares these ports and only these ports as dependency
and antidependency respectively, and does nothing but relay the value from its input to its output.

Therefore, we call such a reaction a relay reaction:

```lean
def Reaction.relay (src dst : ι) : Reaction ι υ := {
  deps := λ r => match r with | Role.in => Finset.singleton src | Role.out => Finset.singleton dst,
  triggers := Finset.singleton src,
  children := ∅,
  body := λ p _ => match p[src] with | none => [] | some v => [Change.port dst v],
  tsSubInDeps := ...,
  outDepOnly := ...,
  normNoChild := ...
}
```

In order to behave exactly as desired, relay reactions also require some special treatment within reactors.

## `Reactor`

The way in which we define `Reactor` is fundamentally different from `Change` and `Reaction`.
In the document on the [Formalization Structure](1.%20Formalization%20Structure.md) we determined that one of the
components in the mutually inductive cycle can't be sealed off from `Raw`-land by plain redefinition (as we did
with `Change` and `Reaction`), but instead has to use "API-tricks" to appear "proper". This burden falls on the 
`Reactor` type. That is, while we would like `Reactor` to be defined as:

```lean
-- This is not how the Reactor type is actually defined!
structure Reactor (ι υ) [ID ι] [Value υ] where
  ports : Ports ι υ   
  roles : ι ▸ Ports.Role
  state : StateVars ι υ
  nest : ι ▸ Reactor ι υ
  rcns : ι ▸ Reaction ι υ
  prios : PartialOrder ι
  constraints : ....
```

... we have to build it as an extension of:

```lean
-- Components/Raw.lean

inductive Raw.Reactor (ι υ) [i : ID ι] [v : Value υ]
  | mk 
    (ports : Ports ι υ) 
    (roles : ι ▸ Ports.Role)
    (state : StateVars ι υ)
    (rcns : ι → Option (Raw.Reaction ι υ))
    (nest : ι → Option (Raw.Reactor ι υ))
    (prios : PartialOrder ι)
```

Thus, our goal is to extend `Raw.Reactor` in such a way that it can be used just as if it were defined in the "pretty" (structure-based) way above.
The key step towards creating a "proper" reactor is the definition of `Raw.Reactor.wellFormed` (the `wf` property in `Reactor`):

```lean
-- Components/Reactor/Basic.lean

structure Raw.Reactor.wellFormed (σ : Raw.Reactor ι υ) : Prop where
  direct : σ.directlyWellFormed 
  offspring : ∀ {rtr : Raw.Reactor ι υ}, σ.isAncestorOf rtr → rtr.directlyWellFormed

structure Reactor (ι υ) [ID ι] [Value υ] where
  fromRaw ::
    raw : Raw.Reactor ι υ
    rawWF : raw.wellFormed  
```

> Side note: 
> The `fromRaw ::` names the constructor of `Reactor`.
> We do this so that we can later define a "proper" constructor called `mk` (which is
> the canonical name for structure constructors).

This property ensures "properness" in two steps:

1. `direct` ensures that the given reactor satisfies all constraints required for a "proper" reactor, bundled as `Raw.Reactor.directlyWellFormed` (more on this later).
2. `offspring` ensures that all nested and creatable reactors also satisfy `directlyWellFormed`. The `isAncestorOf` relation formalizes the notion of (transitive) nesting and "creatability":

### Ancestor Relation

```lean
inductive Raw.Reactor.isAncestorOf : (Raw.Reactor ι υ) → (Raw.Reactor ι υ) → Prop 
  | nested {parent child i} : (parent.nest i = some child) → isAncestorOf parent child
  | creatable {old new rcn p s i iᵣ} : (old.rcns i = some rcn) → (Change.create new iᵣ ∈ rcn.body p s) → isAncestorOf old new
  | trans {r₁ r₂ r₃} : (isAncestorOf r₁ r₂) → (isAncestorOf r₂ r₃) → (isAncestorOf r₁ r₃)
```

Nesting and creatability capture the two types of recursion that appear in our type dependency graph:

![Type Dependencies](images/type-dependencies.png)

The `Raw.Reactor` type is dependent on itself (the loop from reactor to itself), because it can contain nested reactors.
It is further dependent on itself by mutual recursion through `Raw.Change` and `Raw.Reaction`, as a reactor contains reactions
which can produce a `Raw.Change.create` which references the `Raw.Reactor` type.
Thus, there exist two ways in which a reactor can be the "offspring" of another reactor - so `r₁.isAncestorOf r₂` holds if:

* `nested`: `r₁` contains `r₂` directly as nested reactor
* `creatable`: there exists a reaction in `r₁` which can produce a `Raw.Change.create` which contains `r₂`

The `isAncestorOf.trans` case simply forms the transitive closure of the previous cases.

If we now reconsider the `wellFormed.offspring` property:

```lean
offspring : ∀ {rtr : Raw.Reactor ι υ}, σ.isAncestorOf rtr → rtr.directlyWellFormed
```

... it states that any reactor `rtr` that is nested in or creatable by the (parent) reactor `σ` has to be `directlyWellFormed`.
An immediate consequence of this definition is that any offspring reactor is in fact itself `wellFormed`:

```lean
theorem Raw.Reactor.isAncestorOf_preserves_wf
  {rtr₁ rtr₂ : Raw.Reactor ι υ} (ha : rtr₁.isAncestorOf rtr₂) (hw : rtr₁.wellFormed) :
  rtr₂.wellFormed := ...
```

### Direct Well-Formedness

Direct well-formedness captures all of the constraints that need to hold for *all* components contained in a given reactor.

```lean
structure Raw.Reactor.directlyWellFormed (rtr : Raw.Reactor ι υ) : Prop where
  rcnsFinite :      ...
  rcnsWF :          ...
  wfNormDeps :      ...
  ...
  mutsLinearOrder : ...
  uniqueIDs :       ...
```

We will use these constraints to build projections on `Reactor` (more on that in [Raw Lifting](3.%20Raw%20Lifting.md))
that allow us to use it as if it were defined the "pretty" (structure-based) way (demonstrated above).
The constraints can be separated into three different categories: reaction constraints, reactor constraints, ID constraints.

#### Reaction Constraints

As a `Raw.Reactor` only contains `Raw.Reactions`, a "proper" `Reactor` (well-formed `Raw.Reactor`) needs to impose constraints
that allow us to turn `Raw.Reaction`s into "proper" `Reaction`s.
In [`Reaction` (and Mutations)](#reaction-and-mutations) above, we've seen the constraints imposed by `Reaction`. Thus,
`directlyWellFormed` simply mimics these constraints with:

```lean
structure Raw.Reactor.directlyWellFormed (rtr : Raw.Reactor ι υ) : Prop where
  ...
  rcnsWF : ∀ {rcn}, (∃ i, rtr.rcns i = some rcn) → rcn.wellFormed
  ...

structure Raw.Reaction.wellFormed (rcn : Raw.Reaction ι υ) : Prop where
  tsSubInDeps : rcn.triggers ⊆ rcn.deps Role.in                                     
  outDepOnly :  ∀ i s {o} (v : υ), (o ∉ rcn.deps Role.out) → (Change.port o v) ∉ (rcn.body i s)
  normNoChild : rcn.isNorm → rcn.children = ∅
```

#### Reactor Constraints

Reactor constraints can vaguely be classified as those constraints that would be part of the `Reactor` type, if we could declare
it in the "pretty" (structure-based) way (demonstrated above).
Reactor constraints include things like the finiteness of contained reactions and nested reactors:

```lean
structure Raw.Reactor.directlyWellFormed (rtr : Raw.Reactor ι υ) : Prop where
  ...
  rcnsFinite :     { i | rtr.rcns i ≠ none }.finite
  nestFiniteRtrs : { i | rtr.nest i ≠ none }.finite
  ...
```

These constraints will be used to turn the partial functions `Raw.Reactor.rcns` and `Raw.Reactor.nest` into proper `Finmap`s.
Another example of a reactor constraint is: 

```lean
structure Raw.Reactor.directlyWellFormed (rtr : Raw.Reactor ι υ) : Prop where
  ...
  wfMutDeps : ∀ m i, rtr.rcns i = some m → m.isMut → (m.deps Role.in ⊆ (rtr.ports' Role.in).ids) ∧ (↑(m.deps Role.out) ⊆ ↑(rtr.ports' Role.out).ids ∪ {i | ∃ j x, rtr.nest j = some x ∧ i ∈ (x.ports' Role.in).ids})
  ...
```

It constrains the anti-/dependencies of mutations.
Note that this and some other constraints are quite complicated in their type.
This is because they're defined over `Raw` components for which we don't (want to) declare many conveniences.
In [Raw Lifting](3.%20Raw%20Lifting.md) we will "clean up" these constraints by proving analogous statements for "proper" types.

#### ID Constraints

In the document on [Hierarchy Accessors](4.%20Hierarchy%20Accessors.md) we show how to define means of accessing objects within an
entire reactor hierarchy, instead of just a single reactor.
The functionality of these hierarchy accessors is predicated on the fact that all identifiable components have a unique ID.
Thus, a well-formed reactor also enforces this constraint:

```lean
structure Raw.Reactor.directlyWellFormed (rtr : Raw.Reactor ι υ) : Prop where
  uniqueIDs : ∀ l₁ l₂ : Lineage rtr i, l₁ = l₂ 
  ...
```

The constraint is expressed by stating that all `Lineage`s of ID `i` are the same, i.e. there exists at most one.
A `Lineage` for a given ID `i` in the context of a (raw) reactor `σ` is a structure that traces a path through the 
nested reactors of `σ` that lead to the component identified by `i`:

```lean
inductive Raw.Reactor.Lineage : Raw.Reactor ι υ → ι → Type _ 
  | rtr σ i : σ.nest i ≠ none → Lineage σ i
  | rcn σ i : σ.rcns i ≠ none → Lineage σ i
  | prt σ i : i ∈ σ.ports.ids → Lineage σ i
  | stv σ i : i ∈ σ.state.ids → Lineage σ i
  | nest (σ : Raw.Reactor ι υ) {σ'} (i i') : (Lineage σ' i) → (σ.nest i' = some σ') → Lineage σ i
```

A `Lineage` captures two important aspects:

1. The non-recursive constructors (`rtr`, `rcn`, `prt` and `stv`) tell us what kind of component is identified by `i`.
2. The recursive `nest` constructor captures all of the reactors `σ'` that need to be traversed from the root reactor `σ`
   to arrive at the immediate parent of `i`.

As a result, if all lineages for a given ID `i` are forced to be equal (by `uniqueIDs`), then by (2) there can only be
one reactor that contains a component identified by `i` and by (1) there can only be one kind of component identified
by `i`. Thus, `i` must identify a unique component in a unique reactor.

---

Beyond these well-formedness constraints, there's nothing else that differentiates a `Raw.Reactor` from a "proper" `Reactor`.
Hence, if we want the `Reactor` type to hide all of its `Raw` underpinnings, we need to add properties that expose only proper types
instead of their `Raw` counterparts. This is what we look at in [Raw Lifting](3.%20Raw%20Lifting.md).

