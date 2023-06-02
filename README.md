# Reactor Model

This repository contains a [Lean](https://github.com/leanprover/lean4)-based formalization of the _Reactor model_ - a model of computation underlying the [Lingua Franca](https://github.com/icyphy/lingua-franca) language. 

## Resources

While this formalization differs quite significantly from previous work, the following list contains relevant literature covering the Reactor model.

* [Reactors: A Deterministic Model of Concurrent Computation for Reactive Systems (Lohstroh 2020)](https://www2.eecs.berkeley.edu/Pubs/TechRpts/2020/EECS-2020-235.pdf)
* [Reactors: A Deterministic Model for Composable Reactive Systems (Lohstroh et al. 2019)](https://ptolemy.berkeley.edu/publications/papers/19/Lohstroh_etAl_Reactor_CyPhy19_PDFA.pdf)
* [List of related publications by the Lingua Franca community](https://www.lf-lang.org/publications-and-presentations)

## Project Structure

`ReactorModel/Objects` contains definitions and proofs about reactor objects.

`ReactorModel/Execution` contains definitions and proofs for the execution model. Notably `Execution/Theorems/Execution.lean` contains the theorem of determinism and `Execution/Theorems/Progress.lean` the progress theorem.