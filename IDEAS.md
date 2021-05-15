# Ideas

*This file is intended for keeping track of ideas for further formalizations.*

---

### Inst Exec

Remodel determinism:
Prove that there must exist a prec_func and a topo_func.
Hence, prove that there must exist a function that directly computes the execution of an inst-net (without the p and t as input).
Prove that this function is equal to all other run-funcs (this is kind of your theorem of determinism right now).
Use the input-less new run-func for any future formalizations that require inst-exec, like the timed exec below.

Or instead, simply build the choice-rule-acquired prec_func and a topo_func directly into `run`, and prove that it doesnt matter which prec_func and a topo_func choose.

### Timed Execution

1) (Re-)formalize timed execution non-constructively (via propositions).
Have those propositions be akin to reductions like in the lambda calculus.
There will be different kinds of reductions: one for collecting TPAs, one for executing the instantaneous network, one for stepping to the next tag, etc.
A network is then the executed version of another if it is "multi-step reducible" to the other.
Multi-step reduction represents a sequence of reductions, which have to adhere to certain rules:
Certain reductions can only occur before/after others, and some *must* occur before/after certain others.

2) Use Andres Idea of what a computation is, but fit it to your model.
Andres: A computation is a sequence of port-assignments for all ports (kind of like a sequence of big tuples).
You: A computation is a sequence of port- and state assignments. 

Andres' sequence was constrained (in part) by the fact that each consecutive step has to adhere to the single-step rule of computation. 
You can introduce the same. 
Perhaps your concept of a single-step rule can just be defined at the inst-network level, since you've already defined instantaneous execution. 
This would then also lead to your multistep-sequences consisting not of port/state assignments but inst networks. 
The interesting part would be inserting actions into this. 
Perhaps you do need to define a single-step rule that builds on inst. exec. but adds the parts about actions. 

2')

A timed execution is a sequence of instantaneous networks, such that:
* The IAPs are always empty, i.e. the action information is contained in the OAPs. As a result, we don't have to deal with full TPAs (containing more than one tag-value pair) in the IAPs of an inst-network.
* Hence, each inst-network in the sequence is the representation of a network "right after" an inst-computation, and hence at "the end" of that logical time step.
* Hence, timed-networks consist only of an initial inst-network and action-edges (and a proof of their wellformedness), nothing else.
* The rules for which inst-networks can/must follow each other in a timed execution are:
    - Network N+1 must be the network that you get by performing an inst-computation on M, where:
    - M is the same as N, except for the fact that all OAPs are moved to the IAPs. (This is problematic, because the OAPs are then lost.)

Perhaps make timed network exec a sequence of timed networks.
Hence, you "only" need to define single-step (for one logical tag) computation of a network and then have the sequence be concatenation of those.
The crux here is going "moving" the actions.




From an inst network we can create a so-called "action-map". This is a partial function F: port.id -> tag -> option value, such that F(pid, t) = 
* none, if pid is not an OAP
* none, if pid is an OAP and the tpa at pid does not contain a tag-value pair for tag t
* v, if pid is an OAP and the tpa at pid contains a tag-value pair (t, v)

In some inst-network `X`: let `ST` be the smallest tag for which there exists a `pid` with `F(pid, ST) != none`.
A "progressed" network `P` of `X` is a network, where: 
* `P` and `X` are completely equal, except on ports
* all non-action ports of `P` are empty
* all OAPs have the value from before minus any tag-value pair with tag `AT`
* all IAPs `iap` have the value `x`, where x = :
    - none, if `iap` has no connected OAPs
    - `{(ST, F(ST, ih))}`, where:
        ~ if `NN` are all those OAPs `z` connected to `iap` with `F(ST, z) != none`
        ~ then `ih € NN` with the highest priority of all elements in `NN`


### Federated Execution

Formalize time precedence graphs (Lamport clock relation). 