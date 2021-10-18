# Whiteboard

*This file is intended for keeping track of ideas for further formalizations.*

---

## Mutations

* Precedence-acyclicity only ever needs to be checked at the start of an instantaneous execution cycle. Precedence acyclicity is only important in order to be able to find an execution order for mutations and reactions. Hence, even if the execution of a mutation destroys precedence-acyclicity during an instantaneous execution cycle, this is irrelevant for *that* execution cycle. It will only become relevant once the *next* instantaneous execution cycle tries to determine an order of execution. 

* If CREATE is called at *(t, m)*, then any reaction of the newly-created reactor and any reactor in its containment hierarchy that is triggered by • will execute at *(t, m)* also (see start in Algorithm 5), but not before the last mutation of the new reactor’s container has finished executing (see Section 2.6).

* If DELETE (see Algorithm 6) is called at *(t,m)*, then the given reactor is marked for deletion, any of its reactions triggered by ⋄ are queued for execution, and delete is called recursively on all reactors that the given reactor contains. All reactors deleted at *(t, m)* will have their shutdown reactions triggered at *(t, m)*. When the runtime has finished executing all reactions triggered at *(t, m)*, all reactors marked for deletion have any connections that they may still have removed

#### Questions:

1. Add initialization and termination triggers to reactions/mutations?
    * This would also be required to actually define what mutations' reactor-creations and -deletions do.
2. Add stop-request to reactions/mutations?

#### Formalization:

1. There needs to be a constraint that mutations can't affect reactors that are not nested inside the mutation's parent reactor:
    > There are important advantages to limiting the scope of mutations to the internals of a reactor. For example, it allows mutations to be carried out without requiring any coordination with adjacent reactors.
    * This should be a constraint on `Reactor`.
2. There needs to be a separate priority-relation for mutations in `(Raw.)Reactor`.
    > The priority function maps mutations to elements that are strictly less than the elements that it maps reactions to. Thus, a reactor’s mutations will always have precedence over its reactions. The priority set includes a special priority element `*` which is incomparable with the positive integers. It can be assigned to reactions that may execute in arbitrary order and therefore may execute concurrently, but only after all mutations of the reactor have finished executing. (Lohstroh Chapter 2, Remark 4)
    * That is, the priorities of mutations are all ∈ ℤ-, and hence form a linear order.
3. "The outputs of contained reactors are allowed in the dependencies of a reaction, but not in the dependencies of a mutation. This is important because, in contrast to reactions, mutations have the capability of scheduling initialization actions, which do not incur a microstep delay. Disallowing outputs of contained reactors rules out the introduction of undetectable causality loops."
    * "Using CONNECT (see Algorithm 7), a mutation *m* can connect any ports that are in its sources *D(m)* or effects *D∨(m)*, or ports of reactors that it created at runtime."
    * Since the IDs of created reactors' ports can't be added to *D∨(m)* (because of the quote at the start of 3.), there would need to be some other field in `Mutation` that records the IDs of created reactors' ports.
4. Add mutations to `PrecGraph` and adjust the well-formedness conditions to match Algorithm 3 of *Reactors: A Deterministic Model for Composable Reactive Systems* (mind Line 8!). Use the idea from 5 (below) to separate reaction and mutation IDs.

## Federated Execution

Formalize time precedence graphs (Lamport clock relation). 
