# Reactor Model

This repository contains a [Lean](https://github.com/leanprover-community/lean)-based formalization of a subset of the Reactor model (cf. [Lingua Franca](https://github.com/icyphy/lingua-franca)), as well as proofs about its properties.

## Resources

* [Documentation](https://github.com/marcusrossel/reactor-model/tree/main/docs)
* [Bachelor Thesis: *Provable Determinism in Reactors*](https://github.com/marcusrossel/bachelors-thesis/blob/main/Thesis/Thesis.pdf)
* [Bachelor Thesis Defense](https://github.com/marcusrossel/bachelors-thesis/blob/main/Talks/Defense/talk.pdf)
* [Talk about Lean](https://github.com/marcusrossel/bachelors-thesis/blob/main/Talks/Lean/talk.pdf)

## Project Structure

The root folder contains formalizations, which are not specific to reactors:

- `lgraph.lean` defines L-graphs, including the definitions of paths and acyclicity.

- `topo.lean` defines (complete) topological orderings, and proves important lemmas about them.

- `mathlib.lean` contains lemmas about structures from Mathlib, which are not (yet) part of Mathlib. These lemmas were all proven by Yakov Pechersky.

The `timed` folder contains definitions about timed reactor networks.

- `basic.lean` defines tags, TPAs, and timed networks.

- `exec.lean` contains definitions for the timed execution model, i.e. `execution`, `is_time_step`, ..., as well as the proof of timed determinism.

The `inst` folder contains definitions about instantaneous reactors.

- `primitives.lean` defines state variables, ports, and many other definitions/lemmas about ports which were not discussed in this thesis, such as *port-roles* and *inhabited indices*.

- `reaction.lean` defines reactions and their triggering condition.

- `reactor.lean` defines reactors, operations for mutating them, a procedure for executing a reaction in them, reactor equivalence, and *relative equality* (another concept omitted in this thesis).

The `inst/network` folder defines notions about instantaneous reactor *networks*.

- `ids.lean` defines reactor-, reaction- and port-IDs.

- `graph.lean` defines instantaneous reactor network graphs, operations for mutating them, a procedure for executing a reaction locally (without output propagation), and network graph equivalence.

- `basic.lean` expands on `graph.lean` by defining full instantaneous networks, as well as lifting some notions from network graphs to networks.

- `prec.lean` defines precedence graphs, their property of well-formedness, the network property `is_prec_acyclic`, and proves the equality of well-formed precedence graphs.

The `inst/exec` folder defines the execution model for instantaneous networks.

- `run.lean` defines the `run` function, as well as the proof of determinism.

- `topo.lean` defines `run_topo` and `run_reaction`, as well as the corresponding proofs `run_topo_comm`, `run_topo_swap` and `run_reaction_comm`.

- `propagate.lean` defines all of the propagation functions.

- `algorithms.lean` defines the “implicit” algorithms, i.e. `prec_func` and `topo_func`, as well as the proof that all `prec_func`s are equal.
