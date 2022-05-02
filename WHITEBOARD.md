# Whiteboard

## Andrés' Update

* Pure reactions (`Reaction.isPure`), why and how they're used in reactors (its constraints).

* We're at the point where we'd want to use some of the reactor-wf-properties, which have not been lifted yet.

* The `Identified` and `Rooted` types.

* Explain `Get.lean`:
  - `Reactor.cmp?`
  - `Reactor.con?` & `Container`
  - `Reactor.obj?`
  - `Reactor.obj?'`
  - `Reactor.contains`

* `Dependency.lean`:
  - What are the possible dependencies and why are they formalized in this way? 
    (How is obj? and con? used. How does their redundancy manifest itself.)
  - (ir)reflexivity
  - `Indep`:
    - What are the properties derived from Indep.

* `State.lean`:
  - Func fact: `allows_requires_acyclic_deps`
  - Definitions of `rcnInput` and `rcnOutput`
    - related theorems

* Determinism:
  - Plan for `InstExecution.deterministic`
    - We want to state facts about the reactions/changes in InstExecution, InstStep, ChangeListStep, ChangeStep.
      Hence, we need to be able to refer to reactions/changes used in those steps.
      Since the steps live in Prop, we can't define properties like `InstExecution.rcns : InstExecution -> List ID`.
      The best we could do would be `Exists rcns : List ID, ...`, but the `...` would basically be the def of `InstExecution` again.
      To fix this we raise the reaction(s)/change(s) (lists) into the type of `InstExecution` etc. 
  - Current WIP: `InstStep.indep_rcns_indep_output`
  - Fun fact: `InstStep.acyclic_deps`