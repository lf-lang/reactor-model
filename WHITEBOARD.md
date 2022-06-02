# Whiteboard

## Technical Report

1. Why did we define `ID` and `Value` the way we did?
  * Why did we move away from "simple" dependent types? (they were annoying to spell out, and we never instantiate the parameters)
2. Why did we define `Reaction` the way we did? 
  * Why do reactions have the constraints they do? 
    -> Explain the separation between constraints on the objects vs. constraints enforced by the operational semantics.
  * What are `Change`s?
  * Mutations vs. normal reactions.
  * Interaction of priorities and pure reactions (and the role of relay reactions in this + we didn't want to make an exception *only* for relay reactions -> pure).
2. Why did we define `(Raw.)Reactor` the way we did?
  * Everything is a finmap from ID to the component -> this is so we can easily define hierarchy accessors as well as the update relation.
  * Recursive type -> can't be a structure.
  * Nested inductives -> can't have the constraints in the type yet.
  * How to rectify this issue through raw-proper-lifting (mention related efforts - e.g. QPFs).
    * give definition of `WellFormed` and `Reactor` and go into `WellFormed.Direct` in next section
3. What constraints do we place on reactors? (only show the lifted versions?)
  * Technicality: we have to express constraints in terms of raw reactors first, which is annoying. the lifted constraints are expressed in a nicer way.
  * How to get ID-uniqueness any why we need it (Lineages)?
  * "reactor constraints" are constraints that constrain a reactors components, and only make sense in the context of a reactor (that's why we couldn't put the into the definition of `Reaction`)
4. We've defined reactors, now we need tools to work with them -> hierarchy accessors
  * Why can't we just use the plain accessors on reactors?
  * How do we access objects "generically"? -> `Cmp` (that's why we defined reactors as a collection of finmaps from ID to ?_)
  * the `Container` relation and the role of `uniqueIDs` in this
    * Necessity of `Rooted ID` and utility of `Identified Reactor`
  * `con?`, `obj?`, `cmp?` and a vague description of their lemmas
5. Let's define an execution model.
  * First think about what we want the execution model to do in vague terms (or perhaps as pseudo-SOS rules?).
    * E.g. we need to be able to talk about dependencies, we need to capture what reactions have already fired, we need to obtain a reaction's input and output after firing, etc.
  * Then show how our needs are implemented in `Dependency`, `Context` and `State`.
    * Mention why we make an explicit `State`, and what functions we defined on it.
    * What about mutation related things: freshID/freshReactor?
  * Now use these things to define the execution steps.
    * Explain the role of having a relational `Update` instead of a function - especially wrt. mutations.
    * If we *did* implement updates as a function, the formalization for mutations would be:
      1. Add constraints to the `ChangeStep` cases of mutations
      2. Used those constraints to prove the constraints required for the result reactor.
      We would probably choose these constraints on `ChangeStep` in such a way that they precisely allow
      us to prove the reactor constraints - so it's pretty redundant.
      Note that this possibly *could* be used to solve the one-step intermediate-reactor-problem (mentioned below),
      if we combine information about the mutating changes that we want to swap, with the ChangeStep-constraints,
      to prove that both mutations are still possible in the swapped order.
      It doesn't help solve the multi-step intermediate-reactor-problem though, as it is an entirely different lemma
      to show that there exists a *sequence of swaps* from one reaction list to another, such that each required intermediate 
      reactor exists.
6. Proving Determinism
  * What are the possible notions of determinism, which one did we settle on and why.
  * Our variant of determinism is provable if we can simply prove that each `Execution.Step` is deterministic,
    because then we get the result for transitive closure by induction.
  * Proving determinism of `Execution.Step` has two aspects:
    1. We need to show that it's determined whether we can/must take a `completeInst` step vs. an `advanceTime` step.
      * It can be shown immediately that it can't be the case that we have different *kinds* of steps, as their conditions are contradictory.
    2. We need to show that a `completeInst` step is deterministic.
  * Proving that `CompleteInstExecution` is deterministic is again split into two steps:
    1. We show that complete inst executions that start from the same initial state always result in the same context.
      * This is a rather simple consequence of the `complete` property of `CompleteInstExecution`s.
      * Also, clarify why we use "completeness" instead of "stuckness".
    2. We show that `InstExecution`s which lead to the same context are deterministic.
  * Proving `InstExecution.deterministic`
      * This theorem is at the center of the entire proof. So far we haven't needed any properties specific to reactors - now we will need them.
      * Describe what a first/simple approach might be:
        Show that both executions must execute the same reactions -> we get lists of reactions which are permutations of eachother. 
        Then, show that both reaction lists must adhere to dependency constraints.
        Then, show that swapping two independent reactions does not change the result of an execution.
        Then, show that we can stepwise reorder one permutation to the other while preserving dependencies in each step.
        Thus, we get that both reaction lists must execute to the same result.
      * Describe the "intermediate-reactor" problem and show by example why it isn't "solvable" when we have mutations (without mutations it's solvable, as the "success" of each ChangeStep is independent of previous steps (and instead only relies on the structure of the reactor, which doesnt change without mutations)). Also, cf. end of (5.).  
      * Describe the new approach, and how it solves the intermediate-reactor-problem:
        We show equality of the resulting reactors by reasoning about the entire list of changes produced in the execution,
        and showing that they lead to the same results. That is, we're not "creating" any intermediate reactors for our argument.
        1. Define a "structural" notion of equivalent change lists (`ChangeListEquiv`).
        2. Prove that `ChangeListEquiv` implies execution-result-equality.
        3. Show that two `InstExecution`s induce the equivalent change lists (then apply (2) to this).
  * Proving that two `InstExecution`s induce equivalent change lists:
    1. We show that they produce change lists which are permutations of each other.
      * This can be done basically by argumentation on contexts alone.
    2. Show that swapping change lists produced by independent reactions is equivalent to the non-swapped order (`InstStep.indep_rcns_changes_comm_equiv`).
      In our naive proof approach, we were basically forced to "immediately" combine this result with `ChangeListStep.equiv_changes_eq_result`,
      which requires us to give it a proof that executions for the respective change lists exist.
      This gives us the intermediate-reactor-problem, as we don't actually know that an execution of the swapped change list exists.
      But now, we can continue swapping change lists and postpone the usage of `ChangeListStep.equiv_changes_eq_result`,
      until our swaps lead us to the completely permuted execution for which we have a proof of its existence.
    3. Show that there is a sequence of dependency-preserving swaps that leads from one of the initial change lists to the other.
       Thereby, by induction on (2 - kind of) we get that those lists are equivalent, and therefore produce the same result. Qed.   
