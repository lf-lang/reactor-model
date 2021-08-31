# New Foundations

*This documents describes the reasons behind the rewrite of the formalization, started on 23.07.2021 (commit: 809d7063f7d9a907f751a57b9e3311955ef58fcd).*

---

*While proving the existence of a `prec_func`, there were some rough edges around the formalization of instantaneous reactor networks, that made further formalization truly cumbersome. Hence, I believe it to be beneficial to rework some fundamentals before adding new formalizations on top of shaky foundations.
The aim of this document is to lay out the existing problems and present possible benefits of reformalizing some of the fundamentals of instantaneous reactors.*

### Property Access "API"

The current formalization of reactors and networks was very much built on the fly. New definitions were added when a need for them arose. As a result, the definitions for accessing properties on reactions, reactors and networks are somewhat of a patchwork. 

For example, the definition of `reactor` contains two fields for ports: `(input : ports υ)` and `(output : ports υ)`. Later on I noticed that I had to duplicate certain definitions that differed only in the kinds of ports that were being affected (input vs. output). The solution to this was `ports.role`, which allowed definitions *and proofs* to be written in a role-agnostic way. For example:

```lean
-- Updates a given port in the reactor, to hold a given value.
def update (rtr : reactor υ) : ports.role → ℕ → option υ → reactor υ
  | role.input  p v := {input  := rtr.input.update_nth p v,  ..rtr}
  | role.output p v := {output := rtr.output.update_nth p v, ..rtr}
```

Since changing the definitions of `reactor` and `reaction` to use `ports.role` natively would have been too big of a change, the dichotomy between using `reactor.input` and `reactor.ports role.input` (as an example) still lingers - even though they are conceptually the same thing.

There are more examples like this, which make proofs a pain as they require conversions between different, conceptually equal, statements.

I think a solution to this problem would be to define a "complete" set of property access definitions, before building further definitions on an object.
As an example, in the case of `reactor` this would consist of accessors for input and output ports as a whole and as individual ports, as well as accessors to get the set of priorities (aka reaction-IDs) and the set of reactions.
Being able to easily access sets that simply contain all of the distinct components of an object should also help with the next issue. 

### Too Much GIGO

[Provable Determinism in Reactors (PDiR)](https://github.com/marcusrossel/bachelors-thesis/blob/main/Thesis/Thesis.pdf) Sections 1.2.2 and 2.3 explain why the formalization of the Reactor model is a bit "loose" sometimes, i.e. why it does not constrain types and functions to always contain/produce *valid* objects. During further formalization, I've noticed that it's a bit too loose sometimes. The result is that "non-loose" definitions can be really hard to work with in proofs. For example, `reaction.rcns_dep_to` defines the set of reactions that have an anti-/dependency-relationship with a given port (the port being identified by its index `∈ ℕ`).
This was originally defined as:

```lean
def rcns_dep_to (rtr : reactor υ) (r : ports.role) (p : ℕ) : set ℕ :=
  { x | p ∈ (rtr.reactions x).deps r }
```

The problem with this definition is that since `reactor.reactions` was defined as `ℕ → reaction υ`, the definition above could produce an infinite set (which conceptually doesn't make sense, as reactors are finite objects).
The `reactor.reactions` were defined this way, because we also defined `reactor.priorities : finset ℕ` and implicitly stated that `reactor.reactions` only need return *valid* objects for all `x ∈ reactor.priorities`.

Hence, the only solution for a definition of `rcns_dep_to` is to constrain `x` to be `∈ reactor.priorities`:

```lean
def rcns_dep_to (rtr : reactor υ) (r : ports.role) (p : ℕ) : set ℕ :=
  { x ∈ rtr.priorities | p ∈ (rtr.reactions x).deps r }
```

Using *this* definition of `rcns_dep_to` inside of other definitions has profound effects on the provability of related lemmas.
Because now, to prove that `rcn ∈ rtr.rcns_dep_to r p` (for some `rcn`, `rtr`, `r` and `p`) we don't only need to show that there is a dependency relationship between `rcn` and `p` (which is generally derivable from `rtr` and `rcn`) - we also need to show that `rcn` is one of the "valid" reactions (one which is obtained from the set of `reaction.priorities`).
This latter fact is generally not part of other definitions and lemmas though, as we usually don't care about the distinction between valid vs. invalid objects.
Hence, proving `rcn ∈ rtr.rcns_dep_to r p` is generically impossible, unless we add constraints to many other definitions "up the chain", to ensure that `rcn` is actually a valid reaction.

In other words, definitions that require valid objects "contaminate" the definitions they interact with.
It would therefore be beneficial to remove the concept of "invalid" objects and tighten the degree of GIGO a bit.
That is, we need to find a space between dependent type hell and full GIGO. I think this space might be optional values.
Using optional values makes it possible to pass any (garbage) input into a function, but removes the need for that function to return a garbage output value.
That is, instead of an *implicit* garbage return value, we get an explicit `none`.
As a result, we can only ever work with valid objects.

### `inst.network.graph` vs. `inst.network`

The formalization of reactor networks builds on a hierarchy of types, which are extended or constrained to get the "next level" network:

`lgraph` → `inst.network.graph` → `inst.network` → `timed.network`

The way in which this is generally formalized is by creating a new structure which has an instance of the "lower" type with additional fields. For example:

```lean
structure inst.network :=
  (η : inst.network.graph υ)
  (unique_ins : η.has_unique_port_ins)
  (prec_acyclic : η.is_prec_acyclic)
```

A major annoyance that comes with this setup is the fact that definitions for `inst.network.graph` have to be manually "lifted" to also be available to `inst.network`. For example:

```lean
noncomputable def rtr (η : inst.network.graph υ) (i : reactor.id) : reactor υ := η.data i

-- Lifted for `inst.network`.
noncomputable def rtr (σ : inst.network υ) : reactor.id → reactor υ := σ.η.rtr
```

This is already the case for over a dozen definitions and lemmas.
Unfortunately there is no general solution to this problem, as not every definition can be trivially lifted (or even lifted at all - cf. [related zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Building.20up.20types)). For example: 

```lean
noncomputable def update_port (η : inst.network.graph υ) (r : ports.role) (p : port.id) (v : option υ) : inst.network.graph υ :=
  η.update_reactor p.rtr ((η.rtr p.rtr).update r p.prt v)

-- Lifted for `inst.network`.
noncomputable def update_port (σ : inst.network υ) (r : ports.role) (p : port.id) (v : option υ) : inst.network υ :=
  {
      η := σ.η.update_port r p v,
      unique_ins := graph.eq_edges_unique_port_ins (refl _) σ.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.update_port_equiv _ _ _ _) σ.prec_acyclic
  }
```

Here the lifted version needs to perform the additional steps of proving that the constraints required by `inst.network` are still met after performing the `inst.network.graph.update_port` (which does not have any constraints to worry about). 

One of the reasons for the separation between `inst.network.graph` and `inst.network` in the current formalization was to make it possible to define operations on `inst.network.graph` without worrying about the constraints of `inst.network`, and later prove the lemmas required to lift them. This was potentially a good idea for the algorithmic implementation of instantaneous execution as it stands now, as this approach required a variety of functions that *mutate* an `inst.network.graph` (therefore making them non-trivial to lift). On the proof-side of things, this was a nuisance though, as one had to constantly deal with the distinction between the definitions on `inst.network.graph` vs. `inst.network` (even though conceptually `inst.network` is just a specific kind of `inst.network.graph`).
I therefore think that the separation between `inst.network.graph` and `inst.network` should be removed.
This would probably also work well with a descriptive formalization of instantaneous execution, as mutating functions shouldn't play any significant role in that.

### Descriptive Definition of Instantaneous Execution

[PDiR](https://github.com/marcusrossel/bachelors-thesis/blob/main/Thesis/Thesis.pdf) Section 3.6 describes why it would be beneficial to have a non-algorithmic description of the instantaneous execution model.
Aside from this, a major benefit of switching to a descriptive formalization would be the reduction in definitions and lemmas regarding mutation of objects.

For example, definitions and lemmas regarding mutation make up a large part of `reactor.lean`, but are only ever used in the formalization of instantaneous execution. 
Also, facts about mutations tend to be hard to prove due to the [Frame Problem](https://en.wikipedia.org/wiki/Frame_problem) (or something similar).
Removing these definitions would make the formalization much more focussed, and (hopefully) easier to prove theorems about.

Also, `prec_func` and `topo_func` are an odd aspect of the current formalization. 
In a descriptive formalization there would be no need for them.

### Benefits of a Reformalization

While the following aspects aren't reasons for reformalizing the foundations of the model, they would be nice side effects of it.

* We could add missing aspects of the reactor model, like mutations, in the process. Since this should happen sooner or later anyway, and would probably require substantial changes to the existing formalization, it could be added cleanly instead of patchworky during a reformalizing of the foundations.
* This would be a great opportunity to create a more detailed (technical) documentation of the formalization than the high-level overview presented in [PDiR](https://github.com/marcusrossel/bachelors-thesis/blob/main/Thesis/Thesis.pdf).