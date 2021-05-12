# Ideas

*This file is intended for keeping track of ideas for further formalizations.*

---

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

### Federated Execution

Formalize time precedence graphs (Lamport clock relation). 