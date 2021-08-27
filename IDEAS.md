# Ideas

*This file is intended for keeping track of ideas for further formalizations.*

---

**Not yet implemented:**

* Reactor networks do not need to be prec_acyclic, instead this is a property checked at runtime.
** Since mutations can make a network non-prec_acyclic, which in turn ends execution, the prec_acyclicity
** must be checked at runtime anyway (during inst or timed exec?) - i.e. the static version doesnt even make
** sense. A benefit of this is that networks can be defined directly, i.e. without this dance:
** def network.graph -> def prec.graph -> def prec_acyclic -> def network

* Prec.graphs as a type are dependent on a fixed network. That way, there only exist wf prec-graphs.
** Note: the conditions on a (wf) precedence graph change with the introduction of nested reactors and mutations.

**Questions:**

* Should the top-level structure be a network or a reactor?
** If reactor, then what replaces timed-networks - i.e. where is the global time/event queue/... placed?

### Federated Execution

Formalize time precedence graphs (Lamport clock relation). 