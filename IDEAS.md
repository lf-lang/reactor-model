# Ideas

*This file is intended for keeping track of ideas for further formalizations.*

---

### Changes

* Lgraph are now based on finmaps
** This removes some GIGO

* IDs are now opaque like values
** This is more generic than nat-based IDs
** Non-generic IDs would probably become a pain in the context of nested reactor networks
** Ports and state_vars are now finmaps from these IDs

* The opaque value type now has an absent member
** This makes the difference between absent and non-existent port more clear (no double optionality)

* Reactions are now a specific kind of mutation

* Reactors only order their reactions and mutations partially, not totally.
** The proof of determinism will probably include a requirement for the degree of partiality.

* Since reactions, mutations, reactors, reactor networks, etc. are not inherently instantaneous, they live in the root directory. The `inst` directory is only concerned with inst execution.

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

* How can the output of a mutation produce a reactor without a cyclic dependency between the definition of mutation and reactor?
** One of the fields in a reactor could be (hash)map of all of the constructable reactors. The mutation would then only have to return an (opaque) identifier that indexes into that map.

### Dependency Structure

```
digraph G {
  network -> lgraph;
  "mutation.output" -> reactor [style=dashed];
  mutation -> "mutation.output";
  reaction -> mutation;
  reactor -> reaction;
  reactor -> mutation;
  reactor -> network;
  network -> reactor;
  "prec.graph" -> network;
}
```

```
digraph G {
  rankdir=LR;

  subgraph cluster_0 {
    "network 3";
    "network 2";
    "network 1";
    "network 0 (.empty)";
    node [style=filled,color=white];
  }

  subgraph cluster_1 {
    "reactor 3";
    "reactor 2";
    "reactor 1";
    "reactor 0";
    node [style=filled];
  }
  
  "reactor 3" -> "network 3" -> "reactor 2" -> "network 2" -> "reactor 1" -> "network 1" -> "reactor 0" -> "network 0 (.empty)";
}
```

### Federated Execution

Formalize time precedence graphs (Lamport clock relation). 